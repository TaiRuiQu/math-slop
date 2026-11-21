module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! The exponential moment bound for the independent choices of divisors.
The proof uses only the quadratic bound for the exponential on `[-1, 1]`. -/

open Finset Real
open scoped BigOperators

namespace PrescribedSWidth

@[expose] public section

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def bernoulliMass (P S : Finset ι) (q : ι → ℝ) : ℝ :=
  (∏ i ∈ S, q i) * ∏ i ∈ P \ S, (1 - q i)

def centeredSum (P S : Finset ι) (q x : ι → ℝ) : ℝ :=
  (∑ i ∈ S, (1 - q i) * x i) + ∑ i ∈ P \ S, -(q i * x i)

def bernoulliVariance (P : Finset ι) (q x : ι → ℝ) : ℝ :=
  ∑ i ∈ P, q i * (1 - q i) * x i ^ 2

theorem centeredSum_eq_sub {P S : Finset ι} (hS : S ⊆ P) (q x : ι → ℝ) :
    centeredSum P S q x = (∑ i ∈ S, x i) - ∑ i ∈ P, q i * x i := by
  unfold centeredSum
  simp_rw [sub_mul, one_mul, sum_sub_distrib, sum_neg_distrib]
  rw [← sum_sdiff hS (f := fun i => q i * x i)]
  ring

theorem bernoulliMass_nonneg {P S : Finset ι} {q : ι → ℝ} (hS : S ⊆ P)
    (hq : ∀ i ∈ P, q i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bernoulliMass P S q := by
  apply mul_nonneg (prod_nonneg fun i hi => (hq i (hS hi)).1)
  exact prod_nonneg fun i hi => sub_nonneg.2 (hq i (mem_sdiff.1 hi).1).2

/-- Independent choices with odds `r i` give the subset product divided by
the product of `1 + r i`. For a prime `p` the odds are `1/√p`. -/
theorem bernoulliMass_eq_normalized_product {P S : Finset ι} (hS : S ⊆ P)
    (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i) :
    bernoulliMass P S (fun i => r i / (1+r i)) =
      (∏ i ∈ S, r i) / ∏ i ∈ P, (1+r i) := by
  have hprod :
      ∏ i ∈ P \ S, (1 - r i / (1+r i)) =
        ∏ i ∈ P \ S, (1 / (1+r i)) := by
    apply prod_congr rfl
    intro i hi
    have h : 0 < 1 + r i := by linarith [hr i (mem_sdiff.1 hi).1]
    field_simp
    ring
  unfold bernoulliMass
  rw [hprod, prod_div_distrib, prod_div_distrib, prod_const_one, ← mul_div_mul_comm,
    mul_one, mul_comm (∏ i ∈ S, (1+r i)), prod_sdiff hS]

theorem bernoulli_exp_moment (P : Finset ι) (q x : ι → ℝ) (lam : ℝ) :
    ∑ S ∈ P.powerset, bernoulliMass P S q * exp (lam * centeredSum P S q x) =
      ∏ i ∈ P, (q i * exp (lam * ((1 - q i) * x i)) +
        (1 - q i) * exp (lam * -(q i * x i))) := by
  rw [Finset.prod_add]
  apply sum_congr rfl
  intro S hS
  simp only [bernoulliMass, centeredSum, mul_add, mul_sum, exp_add, Real.exp_sum,
    Finset.prod_mul_distrib]
  ring

private theorem exp_le_quadratic {u : ℝ} (hu : |u| ≤ 1) :
    exp u ≤ 1 + u + u ^ 2 := by
  have h := (abs_le.1 (Real.exp_bound (n := 2) hu (by decide))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [sq_nonneg u]

private theorem bernoulli_exp_one_le {q v : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : |v| ≤ 1) :
    q * exp ((1 - q) * v) + (1 - q) * exp (-q * v) ≤
      exp (q * (1 - q) * v ^ 2) := by
  have hq0 : 0 ≤ q := hq.1
  have hq1 : q ≤ 1 := hq.2
  have h1q : 0 ≤ 1 - q := by linarith
  have hu₁ : |(1 - q) * v| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg h1q]
    nlinarith [mul_le_mul_of_nonneg_left hv h1q]
  have hu₂ : |-q * v| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hq0]
    nlinarith [mul_le_mul_of_nonneg_left hv hq0]
  calc
    _ ≤ q * (1 + (1-q)*v + ((1-q)*v)^2) +
        (1-q) * (1 + -q*v + (-q*v)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left (exp_le_quadratic hu₁) hq0)
        (mul_le_mul_of_nonneg_left (exp_le_quadratic hu₂) h1q)
    _ = 1 + q * (1 - q) * v ^ 2 := by ring
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (q * (1 - q) * v ^ 2)

theorem bernoulli_exp_moment_le (P : Finset ι) (q x : ι → ℝ) (lam : ℝ)
    (hq : ∀ i ∈ P, q i ∈ Set.Icc (0 : ℝ) 1)
    (hlam : ∀ i ∈ P, |lam * x i| ≤ 1) :
    ∑ S ∈ P.powerset, bernoulliMass P S q * exp (lam * centeredSum P S q x) ≤
      exp (lam ^ 2 * bernoulliVariance P q x) := by
  rw [bernoulli_exp_moment, bernoulliVariance, mul_sum, Real.exp_sum]
  apply prod_le_prod₀
  · intro i hi
    have hq0 : 0 ≤ q i := (hq i hi).1
    have hq1 : 0 ≤ 1 - q i := sub_nonneg.2 (hq i hi).2
    positivity
  · intro i hi
    rw [show lam * ((1 - q i) * x i) = (1 - q i) * (lam * x i) by ring,
      show lam * -(q i * x i) = -q i * (lam * x i) by ring,
      show lam ^ 2 * (q i * (1 - q i) * x i ^ 2) = q i * (1 - q i) * (lam * x i) ^ 2 by ring]
    exact bernoulli_exp_one_le (hq i hi) (hlam i hi)

/-- A two-sided Bernstein-type tail with parameter `lam`. Taking
`lam = T/(2V₀)` gives the loss `T²/(4V₀)` when `variance ≤ V₀`
and each `|lam * x i| ≤ 1`. -/
theorem bernoulli_abs_tail_le (P : Finset ι) (q x : ι → ℝ) {T lam : ℝ}
    (hlam₀ : 0 ≤ lam) (hq : ∀ i ∈ P, q i ∈ Set.Icc (0 : ℝ) 1)
    (hlam : ∀ i ∈ P, |lam * x i| ≤ 1) :
    ∑ S ∈ P.powerset.filter (fun S => T ≤ |centeredSum P S q x|), bernoulliMass P S q ≤
      2 * exp (-lam * T + lam ^ 2 * bernoulliVariance P q x) := by
  have hminus : ∀ i ∈ P, |(-lam) * x i| ≤ 1 := by
    simpa only [neg_mul, abs_neg] using hlam
  have h₁ := bernoulli_exp_moment_le P q x lam hq hlam
  have h₂ := bernoulli_exp_moment_le P q x (-lam) hq hminus
  simp only [neg_sq] at h₂
  have hbound : exp (lam * T) *
      (∑ S ∈ P.powerset.filter (fun S => T ≤ |centeredSum P S q x|), bernoulliMass P S q) ≤
      ∑ S ∈ P.powerset, bernoulliMass P S q *
        (exp (lam * centeredSum P S q x) + exp ((-lam) * centeredSum P S q x)) := by
    rw [mul_sum, sum_filter]
    apply sum_le_sum
    intro S hS
    have hmass := bernoulliMass_nonneg (mem_powerset.1 hS) hq
    split
    · rename_i he
      rw [mul_comm (exp _)]
      apply mul_le_mul_of_nonneg_left _ hmass
      rcases le_abs.1 he with h | h
      · have h' := exp_le_exp.2 (mul_le_mul_of_nonneg_left h hlam₀)
        linarith [exp_pos ((-lam) * centeredSum P S q x)]
      · have h' := exp_le_exp.2 (mul_le_mul_of_nonneg_left h hlam₀)
        rw [mul_neg, ← neg_mul] at h'
        linarith [exp_pos (lam * centeredSum P S q x)]
    · simpa using mul_nonneg hmass (add_nonneg (exp_pos _).le (exp_pos _).le)
  apply (mul_le_mul_iff_of_pos_left (exp_pos (lam*T))).mp
  calc
    _ ≤ _ := hbound
    _ ≤ 2 * exp (lam ^ 2 * bernoulliVariance P q x) := by
      simp only [mul_add, sum_add_distrib]
      linarith
    _ = _ := by
      rw [mul_left_comm (exp _) 2, ← Real.exp_add]
      congr 2
      ring

end

end

end PrescribedSWidth

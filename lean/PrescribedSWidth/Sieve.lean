module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Finite Möbius expansion and the divisor bound for the smoothed sifted sum. -/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset

namespace PrescribedSWidth

@[expose] public section

noncomputable section

/-- Positive integers up to the support cutoff that are coprime to `Q`. -/
def siftedSum (Q cutoff : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ t ∈ (Icc 1 cutoff).filter (fun t => t.Coprime Q), f t

/-- The part of the lattice sum lying on multiples of `d`. -/
def latticeSum (d cutoff : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ t ∈ (Icc 1 cutoff).filter (fun t => d ∣ t), f t

theorem siftedSum_eq_moebius {Q : ℕ} (hQ : Q ≠ 0) (cutoff : ℕ) (f : ℕ → ℝ) :
    siftedSum Q cutoff f = ∑ d ∈ Q.divisors, (μ d : ℝ) * latticeSum d cutoff f := by
  classical
  have hsum (t : ℕ) :
      ∑ d ∈ Q.divisors, (if d ∣ t then (μ d : ℝ) else 0) =
        if t.Coprime Q then 1 else 0 := by
    rw [← sum_filter]
    have hf : Q.divisors.filter (fun d => d ∣ t) = (Q.gcd t).divisors := by
      ext d
      have hg : Q.gcd t ≠ 0 := ne_zero_of_dvd_ne_zero hQ (Nat.gcd_dvd_left _ _)
      simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hQ, hg, and_comm]
    rw [hf]
    have hm := congrArg (fun g : ArithmeticFunction ℤ => g (Q.gcd t))
      ArithmeticFunction.moebius_mul_coe_zeta
    change (μ * (ζ : ArithmeticFunction ℤ)) (Q.gcd t) = (1 : ArithmeticFunction ℤ) _ at hm
    rw [ArithmeticFunction.coe_mul_zeta_apply] at hm
    exact_mod_cast (by simpa [ArithmeticFunction.one_apply, Nat.Coprime, Nat.gcd_comm Q t]
      using hm)
  unfold siftedSum latticeSum
  rw [sum_filter]
  simp_rw [sum_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  calc
    (if t.Coprime Q then f t else 0) = (if t.Coprime Q then 1 else 0) * f t := by
      split <;> simp_all
    _ = (∑ d ∈ Q.divisors, (if d ∣ t then (μ d : ℝ) else 0)) * f t := by rw [hsum]
    _ = _ := by rw [sum_mul]; apply sum_congr rfl; intro d hd; split <;> simp_all

/-- The smaller of the two lattice bounds is an exponential in the log distance. -/
theorem min_lattice_eq {H d : ℝ} (hH : 0 < H) (hd : 0 < d) :
    min 1 (H / d) / Real.sqrt H =
      (Real.sqrt d)⁻¹ * Real.exp (-|Real.log H - Real.log d| / 2) := by
  have hsH := Real.sqrt_pos.2 hH
  have hsd := Real.sqrt_pos.2 hd
  have hexpH : Real.exp (Real.log H / 2) = Real.sqrt H := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hH]
    congr 1
    ring
  have hexpd : Real.exp (Real.log d / 2) = Real.sqrt d := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hd]
    congr 1
    ring
  rcases le_total H d with h | h
  · rw [min_eq_right ((div_le_one hd).2 h), abs_of_nonpos (sub_nonpos.2 (Real.log_le_log hH h))]
    rw [show - -(Real.log H - Real.log d) / 2 = Real.log H / 2 - Real.log d / 2 by ring,
      Real.exp_sub, hexpH, hexpd]
    field_simp
    nlinarith [Real.sq_sqrt hH.le, Real.sq_sqrt hd.le]
  · rw [min_eq_left ((le_div_iff₀ hd).2 (by simpa using h)),
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hd h))]
    rw [show -(Real.log H - Real.log d) / 2 = Real.log d / 2 - Real.log H / 2 by ring,
      Real.exp_sub, hexpH, hexpd]
    field_simp

/-- Equation (12), before normalizing the weights by the Euler product.
The two hypotheses are the bounded-variation and support bounds for each lattice sum. -/
theorem siftedSum_div_sqrt_le {Q cutoff : ℕ} (hQ : Q ≠ 0) {H C : ℝ}
    (hH : 0 < H) (hC : 0 ≤ C) (f : ℕ → ℝ)
    (hvariation : ∀ d ∈ Q.divisors, |latticeSum d cutoff f| ≤ C)
    (hsupport : ∀ d ∈ Q.divisors, |latticeSum d cutoff f| ≤ C * (H / d)) :
    |siftedSum Q cutoff f| / Real.sqrt H ≤ C * ∑ d ∈ Q.divisors,
      (Real.sqrt d)⁻¹ * Real.exp (-|Real.log H - Real.log d| / 2) := by
  rw [siftedSum_eq_moebius hQ, mul_sum]
  apply (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Real.sqrt_nonneg H)).trans
  rw [sum_div]
  apply sum_le_sum
  intro d hd
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_dvd_of_pos (Nat.mem_divisors.1 hd).1 (Nat.pos_of_ne_zero hQ)
  have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [abs_mul, ← min_lattice_eq hH hdpos, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg H)
  calc
    _ ≤ 1 * |latticeSum d cutoff f| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
    _ = |latticeSum d cutoff f| := one_mul _
    _ ≤ C * min 1 (H / d) := by
      rw [mul_min_of_nonneg _ _ hC, le_min_iff, mul_one]
      exact ⟨hvariation d hd, hsupport d hd⟩

/-- The normalization in the law assigning mass proportional to `d⁻¹ᐟ²`. -/
theorem sum_divisorWeights {Q : ℕ} (hQ : Squarefree Q) :
    ∑ d ∈ Q.divisors, (Real.sqrt d)⁻¹ =
      ∏ p ∈ Q.primeFactors, (1 + (Real.sqrt p)⁻¹) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun d => (Real.sqrt d)⁻¹, by simp⟩
  have hf : f.IsMultiplicative :=
    ⟨by simp [f], fun {m n} _ => by
      change (Real.sqrt (↑(m * n) : ℝ))⁻¹ =
        (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]⟩
  exact (hf.prodPrimeFactors_one_add_of_squarefree hQ).symm

/-- The loss in a single Euler factor is quadratic in the departure from the
maximizing phase. Here the phase is measured from that maximum. -/
theorem phase_log_loss {r θ : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 3 / 4) :
    Real.log (1 + r) - Real.log ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤
      8 * r * θ ^ 2 := by
  let v : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  let u := ‖1 + v‖
  have hv : ‖v‖ = r := by
    rw [show v = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from rfl,
      norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr]
  have hu : 1 - r ≤ u := by
    have h := norm_sub_le (1 + v) v
    rw [add_sub_cancel_right, norm_one, hv] at h
    dsimp [u]; linarith
  have hu₀ : 0 < u := by linarith
  have hdiff : (1 + r) ^ 2 - u ^ 2 = 2 * r * (1 - Real.cos θ) := by
    dsimp [u, v]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
    linear_combination (-r^2) * Real.cos_sq_add_sin_sq θ
  have hcos : 2 * (1 - Real.cos θ) ≤ θ ^ 2 := by
    have ht := Real.sin_sq_le_sq (x := θ / 2)
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul'] at ⊢
    nlinarith [Real.cos_sq_add_sin_sq (θ / 2)]
  have hu₂ : 1 / 16 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ u - 1 / 4 by linarith)
      (show 0 ≤ u + 1 / 4 by linarith)]
  have hratio := Real.log_le_sub_one_of_pos
    (div_pos (sq_pos_of_pos (by positivity : 0 < 1 + r)) (sq_pos_of_pos hu₀))
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hratio
  have hb : (1 + r) ^ 2 / u ^ 2 - 1 ≤ 16 * r * θ ^ 2 := by
    rw [show (1 + r) ^ 2 / u ^ 2 - 1 = ((1 + r) ^ 2 - u ^ 2) / u ^ 2 by
      field_simp,
      div_le_iff₀ (sq_pos_of_pos hu₀), hdiff]
    have h₁ := mul_le_mul_of_nonneg_left hcos hr
    have h₂ := mul_le_mul_of_nonneg_left hu₂ (by positivity : 0 ≤ 16 * r * θ ^ 2)
    nlinarith
  exact le_trans (by linarith [hratio] : Real.log (1 + r) - Real.log u ≤
    ((1 + r) ^ 2 / u ^ 2 - 1) / 2) (by linarith)

def resonancePoint (z : ℝ) : ℂ := 1 / 2 + (Real.pi / Real.log z : ℝ) * Complex.I

def phaseDeparture (z p : ℝ) : ℝ := Real.pi - (Real.pi / Real.log z) * Real.log p

theorem eulerFactor_at_resonance {p z : ℝ} (hp : 0 < p) :
    1 - (p : ℂ) ^ (-resonancePoint z) =
      1 + (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * Complex.exp ((phaseDeparture z p : ℂ) * Complex.I) := by
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_log hp.le).symm
  have he : Complex.log (p : ℂ) * (-resonancePoint z) =
      ((-(Real.log p / 2) : ℝ) : ℂ) +
      ((phaseDeparture z p : ℂ) * Complex.I - Real.pi * Complex.I) := by
    rw [hlog]
    unfold phaseDeparture resonancePoint
    push_cast
    ring
  have hs : Real.exp (Real.log p / 2) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), he, Complex.exp_add,
    Complex.exp_sub, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_neg, hs]
  ring

/-- Quantitative comparison with the maximizing Euler product at the
resonant point. The bound is uniform in the set of retained primes. -/
theorem resonant_product_lower (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) (z : ℝ) :
    (∏ p ∈ P, (1 + (Real.sqrt p)⁻¹)) *
        Real.exp (-(8 * ∑ p ∈ P, (Real.sqrt p)⁻¹ * phaseDeparture z p ^ 2)) ≤
      ‖∏ p ∈ P, (1 - (p : ℂ) ^ (-resonancePoint z))‖ := by
  rw [show -(8 * ∑ p ∈ P, (Real.sqrt p)⁻¹ * phaseDeparture z p ^ 2) =
      ∑ p ∈ P, -(8 * (Real.sqrt p)⁻¹ * phaseDeparture z p ^ 2) by
        rw [mul_sum, ← sum_neg_distrib]
        apply sum_congr rfl
        intro p _
        ring, Real.exp_sum, ← prod_mul_distrib, norm_prod]
  apply prod_le_prod₀
  · intro p hp
    positivity
  · intro p hp
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
    let r := (Real.sqrt (p : ℝ))⁻¹
    let θ := phaseDeparture z p
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hsr : (4 / 3 : ℝ) ≤ Real.sqrt p := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4/3)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsmall : r ≤ 3/4 := by
      dsimp [r]
      rw [← one_div, div_le_iff₀ (show 0 < Real.sqrt p by linarith)]
      linarith
    rw [← Complex.ofReal_natCast, eulerFactor_at_resonance (by linarith)]
    change (1+r) * Real.exp (-(8*r*θ^2)) ≤ ‖1 + (r : ℂ) * Complex.exp (θ * Complex.I)‖
    have hv : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr]
    have hlo : 0 < ‖1 + (r : ℂ) * Complex.exp (θ * Complex.I)‖ := by
      have h := norm_sub_le (1 + (r : ℂ) * Complex.exp (θ * Complex.I))
        ((r : ℂ) * Complex.exp (θ * Complex.I))
      rw [add_sub_cancel_right, norm_one, hv] at h
      linarith
    apply (Real.log_le_log_iff (by positivity) hlo).1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    linarith [phase_log_loss (θ := θ) hr hsmall]

end

end

end PrescribedSWidth

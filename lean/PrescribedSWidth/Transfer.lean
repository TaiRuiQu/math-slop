module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-! Signed extraction, progression averaging, and deletion of proper prime powers. -/

open scoped BigOperators ArithmeticFunction.vonMangoldt
open Finset

namespace PrescribedSWidth

@[expose] public section

noncomputable section

/-- A positive average and a uniform upper bound give a lower bound on the number
of terms at least half the lower bound for the average. -/
theorem card_filter_of_signed_sum {ι : Type*} (A : Finset ι) (f : ι → ℝ) {t U : ℝ}
    (ht : 0 ≤ t) (hU : ∀ i ∈ A, f i ≤ U)
    (hmean : 2 * t * (A.card : ℝ) ≤ ∑ i ∈ A, f i) :
    t * (A.card : ℝ) ≤ U * ((A.filter fun i => t ≤ f i).card : ℝ) := by
  let P := A.filter fun i => t ≤ f i
  let M := A.filter fun i => ¬t ≤ f i
  have hsplit : (∑ i ∈ P, f i) + (∑ i ∈ M, f i) = ∑ i ∈ A, f i :=
    sum_filter_add_sum_filter_not _ _ _
  have hP : (∑ i ∈ P, f i) ≤ U * (P.card : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => hU i (mem_filter.1 hi).1
  have hM : (∑ i ∈ M, f i) ≤ t * (M.card : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => (lt_of_not_ge (mem_filter.1 hi).2).le
  have hcard : (M.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset _ _)
  change t * (A.card : ℝ) ≤ U * (P.card : ℝ)
  linarith [mul_le_mul_of_nonneg_left hcard ht]

/-- Weighted sum of the negative or positive shift, with the small-variable
coprimality condition from the Hardy matrix element. -/
def shiftWeight (plus : Bool) (N m : ℕ) : ℝ :=
  if m.Coprime N then Λ (if plus then N + m else N - m) else 0

def twoShift (short : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ short, (Λ m * b m) * (shiftWeight false N m - shiftWeight true N m)

/-- Sign convention for the two unit-class indicators. -/
def unitIndicator {Q : ℕ} (plus : Bool) (a : ZMod Q) (m : ℕ) : ℝ := by
  classical
  exact if IsUnit (if plus then a + m else a - m) then 1 else 0

theorem unitIndicator_neg {Q : ℕ} (a : ZMod Q) (m : ℕ) :
    unitIndicator false (-a) m = unitIndicator true a m ∧
      unitIndicator true (-a) m = unitIndicator false a m := by
  classical
  have h₁ : -a - (m : ZMod Q) = -(a + m) := by ring
  have h₂ : -a + (m : ZMod Q) = -(a - m) := by ring
  change ((if IsUnit (-a - (m : ZMod Q)) then (1 : ℝ) else 0) =
      (if IsUnit (a + (m : ZMod Q)) then 1 else 0)) ∧
    ((if IsUnit (-a + (m : ZMod Q)) then (1 : ℝ) else 0) =
      (if IsUnit (a - (m : ZMod Q)) then 1 else 0))
  rw [h₁, h₂]
  simp only [IsUnit.neg_iff, and_self]

def signedClassSum {Q : ℕ} (short : Finset ℕ) (b : ℕ → ℝ) (a : ZMod Q) : ℝ :=
  ∑ m ∈ short, (Λ m * b m) * (unitIndicator false a m - unitIndicator true a m)

theorem signedClassSum_choose_sign {Q : ℕ} (short : Finset ℕ) (b : ℕ → ℝ) (a : ZMod Q) :
    ∃ a' ∈ ({a, -a} : Finset (ZMod Q)),
      signedClassSum short b a' = |signedClassSum short b a| := by
  classical
  by_cases h : 0 ≤ signedClassSum short b a
  · exact ⟨a, by simp, (abs_of_nonneg h).symm⟩
  · refine ⟨-a, by simp, ?_⟩
    rw [abs_of_neg (lt_of_not_ge h), signedClassSum, signedClassSum, ← sum_neg_distrib]
    exact sum_congr rfl fun m _ => by
      rw [(unitIndicator_neg a m).1, (unitIndicator_neg a m).2]
      ring

/-- Two uniform progression estimates for each fixed small variable yield the
weighted estimate. `classes m` is 1 for a single class and `ν(m)` after the CRT filter. -/
theorem twoShift_sum_error {Q : ℕ} (A short : Finset ℕ) (b : ℕ → ℝ) (a : ZMod Q)
    (classes : ℕ → ℝ) (main err : ℝ)
    (hAP : ∀ m ∈ short, ∀ plus : Bool,
      |(∑ N ∈ A, shiftWeight plus N m) - main * classes m * unitIndicator plus a m| ≤ err) :
    |(∑ N ∈ A, twoShift short b N) -
        main * ∑ m ∈ short, (Λ m * b m) * classes m *
          (unitIndicator false a m - unitIndicator true a m)| ≤
      (2 * err) * ∑ m ∈ short, |Λ m * b m| := by
  simp only [twoShift]
  rw [sum_comm]
  simp_rw [← mul_sum, sum_sub_distrib]
  rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  rw [show (Λ m * b m) * ((∑ N ∈ A, shiftWeight false N m) -
        (∑ N ∈ A, shiftWeight true N m)) -
        main * ((Λ m * b m) * classes m * (unitIndicator false a m - unitIndicator true a m)) =
      (Λ m * b m) *
      (((∑ N ∈ A, shiftWeight false N m) - main * classes m * unitIndicator false a m) -
       ((∑ N ∈ A, shiftWeight true N m) - main * classes m * unitIndicator true a m)) by ring,
    abs_mul, mul_comm (2 * err)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have htri := abs_add_le
    ((∑ N ∈ A, shiftWeight false N m) - main * classes m * unitIndicator false a m)
    (-((∑ N ∈ A, shiftWeight true N m) - main * classes m * unitIndicator true a m))
  rw [abs_neg, ← sub_eq_add_neg] at htri
  refine htri.trans ?_
  linarith [hAP m hm false, hAP m hm true]

/-- Pointwise bound used in the count of exceptions. -/
theorem abs_twoShift_le (short : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hplus : ∀ m ∈ short, Λ (N + m) ≤ L)
    (hminus : ∀ m ∈ short, Λ (N - m) ≤ L) :
    |twoShift short b N| ≤ L * ∑ m ∈ short, |Λ m * b m| := by
  unfold twoShift
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  rw [abs_mul, mul_comm L]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold shiftWeight
  split
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact abs_le.2 ⟨by linarith [hplus m hm, ArithmeticFunction.vonMangoldt_nonneg (n := N - m)],
      by linarith [hminus m hm, ArithmeticFunction.vonMangoldt_nonneg (n := N + m)]⟩
  · simpa using hL

def primePairIndices (short : Finset ℕ) (N : ℕ) : Finset ℕ :=
  short.filter fun m => m.Prime ∧ (N-m).Prime

/-- Subtract the two proper-prime-power contributions from a positive matrix sum.
The two input estimates can overcount pairs where both sides are proper powers. -/
theorem twoShift_le_primePairCount (short : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    {E₁ E₂ pairBound : ℝ} (hb : ∀ m ∈ short, 0 ≤ b m)
    (h₁ : (∑ m ∈ short.filter (fun m => ¬m.Prime), Λ m * b m * shiftWeight false N m) ≤ E₁)
    (h₂ : (∑ m ∈ short.filter (fun m => ¬(N-m).Prime), Λ m * b m * shiftWeight false N m) ≤ E₂)
    (hp : ∀ m ∈ primePairIndices short N, Λ m * b m * shiftWeight false N m ≤ pairBound) :
    twoShift short b N ≤ pairBound * ((primePairIndices short N).card : ℝ) + E₁ + E₂ := by
  let w := fun m => Λ m * b m * shiftWeight false N m
  have hnonneg (m : ℕ) (hm : m ∈ short) : 0 ≤ w m := by
    have hshift : 0 ≤ shiftWeight false N m := by
      unfold shiftWeight
      split <;> positivity
    exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hb m hm)) hshift
  have hB : twoShift short b N ≤ ∑ m ∈ short, w m := by
    apply sum_le_sum
    intro m hm
    have hshift : 0 ≤ shiftWeight true N m := by
      unfold shiftWeight
      split <;> positivity
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hshift)
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hb m hm))
  have hsplit : (∑ m ∈ short, w m) ≤ (∑ m ∈ primePairIndices short N, w m) +
      (∑ m ∈ short.filter (fun m => ¬m.Prime), w m) +
      (∑ m ∈ short.filter (fun m => ¬(N-m).Prime), w m) := by
    simp only [primePairIndices, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro m hm
    have h := hnonneg m hm
    by_cases hl : m.Prime <;> by_cases hr : (N-m).Prime <;> simp [hl, hr]
    all_goals linarith
  have hpair : (∑ m ∈ primePairIndices short N, w m) ≤
      pairBound * ((primePairIndices short N).card : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hp
  linarith

end

end

end PrescribedSWidth

module

public import PrescribedSWidth.Transfer
public import PrescribedSWidth.Spectral
public import PrescribedSWidth.SingularSeries
import Mathlib.Tactic

/-! Quantitative extraction of exceptional moduli and the two prescribed-width
corollaries. The progression estimates and the mixed Hardy test enter as
explicit hypotheses at the points where they are used. -/

open ConditionalGoldbach Filter Finset Real
open scoped BigOperators ArithmeticFunction.vonMangoldt

@[expose] public section

noncomputable section

namespace PrescribedSWidth

attribute [local instance] Classical.propDecidable

def dyadicEven (X : ℝ) : Finset ℕ :=
  (Icc ⌈X⌉₊ ⌊2*X⌋₊).filter Even

theorem mem_dyadicEven_iff {X : ℝ} {N : ℕ} (hX : 0 ≤ X) :
    N ∈ dyadicEven X ↔ Even N ∧ X ≤ (N : ℝ) ∧ (N : ℝ) ≤ 2 * X := by
  simp [dyadicEven, mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith : 0 ≤ 2*X),
    and_comm]

/-- Extract a family from individual shifted progression estimates. In the
unfiltered case `classes = 1`. With the auxiliary coprimality restriction it
counts the admissible residue classes from the CRT. -/
theorem card_of_progression_average {Q : ℕ} (A short : Finset ℕ) (b : ℕ → ℝ)
    (a : ZMod Q) (classes : ℕ → ℝ) (main err t U : ℝ) (P : ℕ → Prop)
    [DecidablePred P] (ht : 0 ≤ t) (hU : 0 ≤ U)
    (hAP : ∀ m ∈ short, ∀ plus : Bool,
      |(∑ N ∈ A, shiftWeight plus N m) - main * classes m * unitIndicator plus a m| ≤ err)
    (hmain : 2*t*(A.card : ℝ) + (2*err)*(∑ m ∈ short, |Λ m * b m|) ≤
      main * ∑ m ∈ short, (Λ m * b m) * classes m *
        (unitIndicator false a m - unitIndicator true a m))
    (hpoint : ∀ N ∈ A, twoShift short b N ≤ U)
    (hgood : ∀ N ∈ A, t ≤ twoShift short b N → P N) :
    t * (A.card : ℝ) ≤ U * ((A.filter P).card : ℝ) := by
  have herr := (abs_le.1 (twoShift_sum_error A short b a classes main err hAP)).1
  have hmean : 2*t*(A.card : ℝ) ≤ ∑ N ∈ A, twoShift short b N := by linarith
  have hcard := card_filter_of_signed_sum A (twoShift short b) ht hpoint hmean
  have hsub : A.filter (fun N => t ≤ twoShift short b N) ⊆ A.filter P := by
    intro N hN
    have hm := mem_filter.1 hN
    exact mem_filter.2 ⟨hm.1, hgood N hm.1 hm.2⟩
  exact hcard.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub) hU)

/-- The matrix-element estimate propagates the signed threshold to the stated
bound on Li–Liu's actual operator. `D` is a positive constant times `√H`
when the short weight has `M = 10H`. -/
theorem strongNormBound_of_twoShift {N : ℕ} {short : Finset ℕ} {b : ℕ → ℝ}
    {C D t : ℝ} (hD : 0 < D)
    (ht : D * exp (normExponent C (log N)) ≤ t)
    (hB : t ≤ twoShift short b N)
    (hHardy : ∀ (_ : NeZero N) (ha : alpha N < beta),
      twoShift short b N ≤ D * (sqrt N * ‖residualOperator ha N‖)) :
    StrongNormBound C N := by
  intro inst ha
  exact (mul_le_mul_iff_of_pos_left hD).1 (ht.trans (hB.trans (hHardy inst ha)))

/-- A bound `t · #A / U` from the signed progression carries over to the
cardinality of the exceptional set in the full interval `[X,2X]`. -/
theorem card_normBound_of_progression_average {Q : ℕ} {X C D : ℝ}
    (A short : Finset ℕ) (b : ℕ → ℝ) (a : ZMod Q) (classes : ℕ → ℝ) (main err t U : ℝ)
    (hA : A ⊆ dyadicEven X) (ht : 0 ≤ t) (hU : 0 < U) (hD : 0 < D)
    (hAP : ∀ m ∈ short, ∀ plus : Bool,
      |(∑ N ∈ A, shiftWeight plus N m) - main * classes m * unitIndicator plus a m| ≤ err)
    (hmain : 2*t*(A.card : ℝ) + (2*err)*(∑ m ∈ short, |Λ m * b m|) ≤
      main * ∑ m ∈ short, (Λ m * b m) * classes m *
        (unitIndicator false a m - unitIndicator true a m))
    (hpoint : ∀ N ∈ A, twoShift short b N ≤ U)
    (hthreshold : ∀ N ∈ A, D * exp (normExponent C (log N)) ≤ t)
    (hHardy : ∀ N ∈ A, ∀ (_ : NeZero N) (ha : alpha N < beta),
      twoShift short b N ≤ D * (sqrt N * ‖residualOperator ha N‖)) :
    t * (A.card : ℝ) / U ≤ (((dyadicEven X).filter (StrongNormBound C)).card : ℝ) := by
  apply (div_le_iff₀ hU).2
  have h₂ := card_of_progression_average A short b a classes main err t U
    (StrongNormBound C) ht hU.le hAP hmain hpoint
    (fun N hN hB => strongNormBound_of_twoShift hD (hthreshold N hN) hB (hHardy N hN))
  have hsub : A.filter (StrongNormBound C) ⊆ (dyadicEven X).filter (StrongNormBound C) :=
    filter_subset_filter _ hA
  rw [mul_comm _ U]
  exact h₂.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub) hU.le)

/-- If the two proper-power masses are small, the very same signed threshold
selects moduli with many true prime pairs. -/
theorem primePairCount_of_twoShift (short : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    {t target E₁ E₂ pairBound : ℝ} (hb : ∀ m ∈ short, 0 ≤ b m)
    (h₁ : (∑ m ∈ short.filter (fun m => ¬m.Prime), Λ m * b m * shiftWeight false N m) ≤ E₁)
    (h₂ : (∑ m ∈ short.filter (fun m => ¬(N-m).Prime), Λ m * b m * shiftWeight false N m) ≤ E₂)
    (hpair : ∀ m ∈ primePairIndices short N, Λ m * b m * shiftWeight false N m ≤ pairBound)
    (hpos : 0 < pairBound) (ht : pairBound * target + E₁ + E₂ ≤ t)
    (hB : t ≤ twoShift short b N) :
    target ≤ ((primePairIndices short N).card : ℝ) := by
  apply (mul_le_mul_iff_of_pos_left hpos).1
  linarith [twoShift_le_primePairCount short b N hb h₁ h₂ hpair]

theorem unbounded_normBound_of_interval_counts {C : ℝ} {count : ℝ → ℝ}
    (hc : ∀ᶠ X in atTop, 0 < count X ∧ count X ≤
      (((dyadicEven X).filter (StrongNormBound C)).card : ℝ)) :
    ∀ K : ℕ, ∃ N ≥ K, Even N ∧ StrongNormBound C N := by
  classical
  intro K
  obtain ⟨X, hX, hK⟩ := (hc.and (eventually_ge_atTop (K : ℝ))).exists
  have ht : 0 < (((dyadicEven X).filter (StrongNormBound C)).card : ℝ) := hX.1.trans_le hX.2
  obtain ⟨N, hN⟩ := card_pos.1 (by exact_mod_cast ht)
  have hmem := (mem_dyadicEven_iff ((Nat.cast_nonneg K).trans hK)).1 (mem_filter.1 hN).1
  exact ⟨N, by exact_mod_cast hK.trans hmem.2.1, hmem.1, (mem_filter.1 hN).2⟩

/-- The logarithmic singular-series bound used in the width comparison is
supplied by the finite Euler product. -/
theorem not_hypothesisS_of_unbounded_normBound {a d C : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    (hd : d < 2 + log 2) (hGRH : GlobalGRH)
    (hbound : ∀ K : ℕ, ∃ N ≥ K, Even N ∧ StrongNormBound C N) :
    ¬ HypothesisS (prescribedWidth a d) := by
  let D := 2 * C2 * (1 + (log 2)⁻¹)
  have hC2 := C2_pos
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine not_hypothesisS_of_normBound ha ha' hd hD hGRH ?_ hbound
  exact evenEventually_large.mono fun N hN =>
    singularSeries_le_log (by have := (large_parameters hN).1; omega) (by
      have h := Real.log_lt_log (Real.exp_pos 10) hN
      rw [Real.log_exp] at h
      linarith)

/-- This includes the equality case `d = √2` of the first family. -/
theorem first_width_fails {d C : ℝ} (hd : 0 < d) (hd' : d ≤ sqrt 2) (hGRH : GlobalGRH)
    (hbound : ∀ K : ℕ, ∃ N ≥ K, Even N ∧ StrongNormBound C N) :
    ¬ HypothesisS (prescribedWidth (d / sqrt 2) 0) :=
  not_hypothesisS_of_unbounded_normBound (div_pos hd (by positivity))
    ((div_le_one (by positivity)).2 hd') (by have := Real.log_pos (by norm_num : 1 < (2 : ℝ)); linarith)
    hGRH hbound

theorem second_width_fails {d C : ℝ} (hd : d < 2 + log 2) (hGRH : GlobalGRH)
    (hbound : ∀ K : ℕ, ∃ N ≥ K, Even N ∧ StrongNormBound C N) :
    ¬ HypothesisS (prescribedWidth 1 d) :=
  not_hypothesisS_of_unbounded_normBound one_pos le_rfl hd hGRH hbound

end PrescribedSWidth

end

end

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Localization of the Mellin witness to a window in the logarithmic scale. -/

open MeasureTheory Set Real
open scoped BigOperators

@[expose] public section

noncomputable section

namespace PrescribedSWidth

def logBump (a x : ℝ) : ℝ := exp (-|x-a|/2)

private theorem logBump_left {a x : ℝ} (h : x ≤ a) :
    logBump a x = exp (-(1/2) * a) * exp ((1/2) * x) := by
  rw [logBump, abs_of_nonpos (sub_nonpos.2 h), ← exp_add]
  congr 1
  ring

private theorem logBump_right {a x : ℝ} (h : a ≤ x) :
    logBump a x = exp ((1/2) * a) * exp (-(1/2) * x) := by
  rw [logBump, abs_of_nonneg (sub_nonneg.2 h), ← exp_add]
  congr 1
  ring

theorem integrable_logBump (a : ℝ) : Integrable (logBump a) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := a)]
  apply IntegrableOn.union
  · have heq : EqOn (logBump a) (fun x => exp (-(1/2) * a) * exp ((1/2) * x)) (Iic a) :=
      fun _ h => logBump_left h
    rw [integrableOn_congr_fun heq measurableSet_Iic]
    exact (integrableOn_exp_mul_Iic (by norm_num : 0 < (1/2 : ℝ)) a).const_mul _
  · have heq : EqOn (logBump a) (fun x => exp ((1/2) * a) * exp (-(1/2) * x)) (Ioi a) :=
      fun _ h => logBump_right (mem_Ioi.1 h).le
    rw [integrableOn_congr_fun heq measurableSet_Ioi]
    exact (integrableOn_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0) a).const_mul _

theorem integral_logBump_compl_Icc (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ x in (Icc (a-T) (a+T))ᶜ, logBump a x = 4 * exp (-T/2) := by
  have he : (Icc (a-T) (a+T))ᶜ = Iio (a-T) ∪ Ioi (a+T) := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hd : Disjoint (Iio (a-T)) (Ioi (a+T)) := by
    apply Set.disjoint_left.2
    intro x hx hy
    change x < a-T at hx
    change a+T < x at hy
    linarith
  have h := integrable_logBump a
  rw [he, setIntegral_union hd measurableSet_Ioi h.integrableOn h.integrableOn]
  have hleft : ∫ x in Iio (a-T), logBump a x = 2 * exp (-T/2) := by
    rw [← integral_Iic_eq_integral_Iio]
    rw [setIntegral_congr_fun measurableSet_Iic (fun x hx => logBump_left (by
      change x ≤ a - T at hx; linarith))]
    rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : 0 < (1/2 : ℝ))]
    calc
      _ = 2 * (exp (-(1/2) * a) * exp ((1/2) * (a-T))) := by ring
      _ = _ := by rw [← exp_add, show -(1/2 : ℝ) * a + 1/2 * (a-T) = -T/2 by ring]
  have hright : ∫ x in Ioi (a+T), logBump a x = 2 * exp (-T/2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => logBump_right (by
      change a + T < x at hx; linarith))]
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1/2 : ℝ) < 0)]
    calc
      _ = 2 * (exp ((1/2) * a) * exp (-(1/2) * (a+T))) := by ring
      _ = _ := by rw [← exp_add, show (1/2 : ℝ) * a + -(1/2 : ℝ) * (a+T) = -T/2 by ring]
  rw [hleft, hright]
  ring

theorem integral_logBump (a : ℝ) : ∫ x, logBump a x = 4 := by
  have h := integral_logBump_compl_Icc a (T := 0) le_rfl
  rw [add_zero, sub_zero] at h
  rw [← integral_add_compl measurableSet_Icc (integrable_logBump a), h]
  simp

/-- Absolute mass outside the interval of radius `2T`. The first term comes
from centers within distance `T` and the second from the remaining centers. -/
theorem weighted_logBump_tail {ι : Type*} (D : Finset ι) (w center : ι → ℝ)
    (hw : ∀ i ∈ D, 0 ≤ w i) {μ T : ℝ} (hT : 0 ≤ T) :
    (∫ x in (Icc (μ-2*T) (μ+2*T))ᶜ, ∑ i ∈ D, w i * logBump (center i) x) ≤
      4 * (exp (-T/2) * ∑ i ∈ D, w i) +
        4 * ∑ i ∈ D.filter (fun i => T < |center i - μ|), w i := by
  classical
  let U := (Icc (μ-2*T) (μ+2*T))ᶜ
  have hint (i : ι) : Integrable (fun x => w i * logBump (center i) x) :=
    (integrable_logBump (center i)).const_mul _
  change (∫ x in U, ∑ i ∈ D, w i * logBump (center i) x) ≤ _
  rw [integral_finsetSum D (fun i _ => (hint i).integrableOn),
    ← mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [integral_const_mul]
  by_cases hclose : |center i - μ| ≤ T
  · have hsub : U ⊆ (Icc (center i-T) (center i+T))ᶜ := by
      apply compl_subset_compl.mpr
      intro x hx
      obtain ⟨hc₁, hc₂⟩ := abs_le.1 hclose
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hb := setIntegral_mono_set (integrable_logBump (center i)).integrableOn
      (Filter.Eventually.of_forall (fun _ => (exp_pos _).le)) hsub.eventuallySubset
    rw [integral_logBump_compl_Icc _ hT] at hb
    simpa [not_lt_of_ge hclose, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hb (hw i hi)
  · have hb := setIntegral_mono_set (integrable_logBump (center i)).integrableOn
      (Filter.Eventually.of_forall (fun _ => (exp_pos _).le)) (subset_univ U).eventuallySubset
    rw [setIntegral_univ, integral_logBump] at hb
    have hh := mul_le_mul_of_nonneg_left hb (hw i hi)
    simp only [ite_eq_left (lt_of_not_ge hclose)]
    nlinarith [mul_nonneg (exp_pos (-T/2)).le (hw i hi)]

/-- A lower bound on the entire integral yields a pointwise witness in the
window once its complement contributes at most half that lower bound. -/
theorem exists_in_window_of_integral {K : ℝ → ℂ} (hK : Integrable K)
    {μ T A : ℝ} (hT : 0 < T) (hA : 0 < A)
    (hI : A ≤ ‖∫ x, K x‖)
    (htail : (∫ x in (Icc (μ-2*T) (μ+2*T))ᶜ, ‖K x‖) ≤ A/2) :
    ∃ x ∈ Icc (μ-2*T) (μ+2*T), A/(16*T) ≤ ‖K x‖ := by
  let U := Icc (μ-2*T) (μ+2*T)
  by_contra! h
  have hdom : (∫ x in U, ‖K x‖) ≤ ∫ _ in U, A/(16*T) :=
    setIntegral_mono_on hK.norm.integrableOn
      (integrableOn_const (isCompact_Icc.measure_lt_top.ne)) measurableSet_Icc
      (fun _ hx => (h _ hx).le)
  have hconst : (∫ _ in U, A/(16*T)) = A/4 := by
    simp only [integral_const, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, U, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ μ+2*T - (μ-2*T)),
      smul_eq_mul]
    field_simp
    ring
  rw [hconst] at hdom
  have hnorm := hI.trans (norm_integral_le_integral_norm K)
  rw [← integral_add_compl (s := U) measurableSet_Icc hK.norm] at hnorm
  linarith

end PrescribedSWidth

end

end

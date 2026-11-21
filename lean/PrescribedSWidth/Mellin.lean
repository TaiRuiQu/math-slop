module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! The Mellin identity for the sifted sum, written in the reciprocal scale
`x = 1/H`, and its continuation to the upper half of the right half-plane. -/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

@[expose] public section

noncomputable section

namespace PrescribedSWidth

def dilateSum (c : ℕ → ℂ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, if n = 0 then 0 else c n * F (n * x)

/-- The absolutely convergent Mellin identity for a sum of dilates. -/
theorem mellin_dilateSum {c : ℕ → ℂ} {F : ℝ → ℂ} {s : ℂ}
    (hF : MellinConvergent F s) (hc : LSeriesSummable c s) :
    mellin (dilateSum c F) s = mellin F s * LSeries c s := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * F x
  let G : ℕ → ℝ → ℂ := fun n x => (LSeries.term c s n * (n : ℂ)) * g ((n : ℝ) * x)
  have hi : IntegrableOn g (Ioi (0 : ℝ)) := hF
  have hG (n : ℕ) : IntegrableOn (G n) (Ioi (0 : ℝ)) := by
    by_cases hn : n = 0
    · simp [G, hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hgi : IntegrableOn (fun x => g (n * x)) (Ioi (0 : ℝ)) :=
        (integrableOn_Ioi_comp_mul_left_iff g 0 hn').2 (by simpa using hi)
      exact hgi.const_mul _
  have hnorm (n : ℕ) : (∫ x in Ioi (0 : ℝ), ‖G n x‖) =
      ‖LSeries.term c s n‖ * ∫ x in Ioi (0 : ℝ), ‖g x‖ := by
    by_cases hn : n = 0
    · simp [G, hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [G, norm_mul]
      rw [integral_const_mul, integral_comp_mul_left_Ioi (fun x => ‖g x‖) 0 hn']
      simp only [mul_zero, smul_eq_mul, norm_natCast]
      field_simp
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖G n x‖ := by
    simp_rw [hnorm]
    exact hc.norm.mul_right _
  have hterm (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) (n : ℕ) :
      (x : ℂ) ^ (s - 1) * (if n = 0 then 0 else c n * F (n * x)) = G n x := by
    by_cases hn : n = 0
    · simp [G, hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hp : (n : ℂ) ^ s ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]
        exact fun h => hnC h.1
      simp only [G, g, ite_eq_right hn, LSeries.term_of_ne_zero hn]
      rw [ofReal_mul,
        mul_cpow_ofReal_nonneg hn'.le hx.le, ofReal_natCast,
        cpow_sub s 1 hnC, cpow_one]
      field_simp
  have hGI (n : ℕ) : (∫ x in Ioi (0 : ℝ), G n x) = mellin F s * LSeries.term c s n := by
    by_cases hn : n = 0
    · simp [G, hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      change (∫ x in Ioi (0 : ℝ), (LSeries.term c s n * (n : ℂ)) * g (n * x)) =
        (∫ x in Ioi (0 : ℝ), g x) * LSeries.term c s n
      rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hn']
      simp only [mul_zero, Complex.real_smul, ofReal_inv, ofReal_natCast]
      field_simp
  calc
    mellin (dilateSum c F) s = ∫ x in Ioi (0 : ℝ), ∑' n, G n x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (x : ℂ) ^ (s - 1) * (∑' n : ℕ, if n = 0 then 0 else c n * F (n * x)) = _
      rw [← tsum_mul_left]
      exact tsum_congr (hterm x hx)
    _ = ∑' n, ∫ x in Ioi (0 : ℝ), G n x :=
      (integral_tsum_of_summable_integral_norm hG hsum).symm
    _ = mellin F s * LSeries c s := by simp only [hGI, LSeries, tsum_mul_left]

def reciprocalSiftedSum (Q : ℕ) (F : ℝ → ℂ) : ℝ → ℂ :=
  dilateSum (fun n => (1 : DirichletCharacter ℂ Q) n) F

theorem mellin_reciprocalSiftedSum_of_one_lt {Q : ℕ} [NeZero Q] {F : ℝ → ℂ} {s : ℂ}
    (hF : MellinConvergent F s) (hs : 1 < s.re) :
    mellin (reciprocalSiftedSum Q F) s =
      mellin F s * DirichletCharacter.LFunctionTrivChar Q s := by
  unfold reciprocalSiftedSum
  rw [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries _ hs]
  apply mellin_dilateSum hF
  exact LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => (1 : DirichletCharacter ℂ Q).norm_le_one n) hs

/-- Equation (3) at all `s` with `0 < re s` and `0 < im s`.
The hypotheses on the sifted sum express local integrability, its vanishing
for large reciprocal scale, and the boundedness near zero provided by the
zero-integral lattice estimate. -/
theorem mellin_reciprocalSiftedSum_eq_euler {Q : ℕ} [NeZero Q] {F : ℝ → ℂ}
    (hF : ∀ s, MellinConvergent F s) (hFd : Differentiable ℂ (mellin F))
    (hlocal : LocallyIntegrableOn (reciprocalSiftedSum Q F) (Ioi 0))
    (htop : ∀ a : ℝ, reciprocalSiftedSum Q F =O[atTop] (· ^ (-a)))
    (h₀ : reciprocalSiftedSum Q F =O[𝓝[>] 0] (fun _ => (1 : ℝ)))
    {s : ℂ} (hs : 0 < s.re) (hsi : 0 < s.im) :
    mellin (reciprocalSiftedSum Q F) s =
      mellin F s * riemannZeta s * ∏ p ∈ Q.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  let U := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}
  have hU : Convex ℝ U :=
    (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).inter
      (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0)
  have ho : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hA : AnalyticOnNhd ℂ (mellin (reciprocalSiftedSum Q F)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hr : 0 < z.re := hz.1
    exact (mellin_differentiableAt_of_isBigO_rpow hlocal (htop (z.re + 1)) (by linarith)
      (by simpa using h₀) hr).differentiableWithinAt
  have hB : AnalyticOnNhd ℂ (fun z => mellin F z * DirichletCharacter.LFunctionTrivChar Q z) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hne : z ≠ 1 := fun h => by have := hz.2; simp [h] at this
    exact ((hFd z).mul
      (DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ Q) z
        (Or.inl hne))).differentiableWithinAt
  have hp : (2 + I : ℂ) ∈ U := by simp [U]
  have heq : mellin (reciprocalSiftedSum Q F) =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => mellin F z * DirichletCharacter.LFunctionTrivChar Q z) := by
    have hm : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 + I : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hm] with z hz
    exact mellin_reciprocalSiftedSum_of_one_lt (hF z) hz
  have hne : s ≠ 1 := fun h => by simp [h] at hsi
  rw [hA.eqOn_of_preconnected_of_eventuallyEq hB hU.isPreconnected hp heq (show s ∈ U from ⟨hs,hsi⟩)]
  change mellin F s * DirichletCharacter.LFunctionTrivChar Q s = _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne]
  ring

end PrescribedSWidth

end

end

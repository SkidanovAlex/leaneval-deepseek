import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.Vcoef

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §1. Three elementary facts about the frame vectors -/

/-- Off `Set.range ι` a frame vector is the corresponding basis vector: the Cramer correction
`betaC` only affects the `ι`-coordinates. -/
theorem VcoefC_of_notMem_range (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (i : Fin k) (hi : i ∉ Set.range ι) :
    VcoefC c h ι l z i = if i = l then 1 else 0 := by
  simp only [VcoefC]
  have hsum : (∑ b : Fin j, if ι b = i then betaC c h ι l z b else 0) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    exact if_neg fun hb => hi ⟨b, hb⟩
  rw [hsum, sub_zero]

/-- On the `ιᶜ`-coordinates a combination of frame vectors is the coefficient itself. -/
theorem sum_coeff_mul_VcoefC_of_notMem_range (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (z : Fin k → ℂ) (c' : U k ι → ℂ) (i : Fin k) (hi : i ∉ Set.range ι) :
    (∑ l : U k ι, c' l • VcoefC c h ι l z) i = c' ⟨i, hi⟩ := by
  have hsingle : (∑ l : U k ι, c' l * VcoefC c h ι (l : Fin k) z i)
      = c' ⟨i, hi⟩ * VcoefC c h ι i z i :=
    Finset.sum_eq_single (⟨i, hi⟩ : U k ι)
      (fun l _ hl => by
        have hne : ¬ (i = (l : Fin k)) := fun h => hl (Subtype.ext h.symm)
        rw [VcoefC_of_notMem_range c h ι (l : Fin k) z i hi, if_neg hne]
        ring)
      (fun hmem => absurd (Finset.mem_univ _) hmem)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsingle, VcoefC_of_notMem_range c h ι i z i hi, if_pos rfl, mul_one]

/-- **The tangential frame is linearly independent** at every point: a linear combination of the
frame vectors `VcoefC c h ι l z` (`l : U k ι`) vanishes only if all its coefficients do.  (This is
the second ingredient of the dimension count in the proof of `kernel_frame_rows`.) -/
theorem sum_span_VcoefC_eq_zero (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) {c' : U k ι → ℂ}
    (h0 : ∑ l : U k ι, c' l • VcoefC c h ι l z = 0) : c' = 0 := by
  funext i
  have hi := sum_coeff_mul_VcoefC_of_notMem_range c h ι z c' i i.2
  rw [h0] at hi
  have heta : (⟨i, i.2⟩ : U k ι) = i := Subtype.ext rfl
  rw [← heta]
  exact hi.symm

/-- The span of the tangential frame is contained in the common kernel of the `h`-rows. -/
theorem sum_span_VcoefC_mul (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) (hz : jacValC c h ι z ≠ 0) (c' : U k ι → ℂ) (a : Fin j) :
    ∑ i, (∑ l : U k ι, c' l • VcoefC c h ι l z) i * eaEvalC c (eaD c i (h a)) z = 0 := by
  have h1 : ∀ i : Fin k, (∑ l : U k ι, c' l • VcoefC c h ι l z) i
      = ∑ l : U k ι, c' l * VcoefC c h ι (l : Fin k) z i := by
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ i, (∑ l : U k ι, c' l • VcoefC c h ι l z) i * eaEvalC c (eaD c i (h a)) z
      = ∑ i, (∑ l : U k ι, c' l * VcoefC c h ι (l : Fin k) z i) *
            eaEvalC c (eaD c i (h a)) z := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1 i]
    _ = ∑ i, ∑ l : U k ι, (c' l * VcoefC c h ι (l : Fin k) z i) *
            eaEvalC c (eaD c i (h a)) z := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ l : U k ι, ∑ i, (c' l * VcoefC c h ι (l : Fin k) z i) *
            eaEvalC c (eaD c i (h a)) z := by
        rw [Finset.sum_comm]
    _ = ∑ l : U k ι, c' l *
            (∑ i, VcoefC c h ι (l : Fin k) z i * eaEvalC c (eaD c i (h a)) z) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [VcoefC_tangent c h ι (l : Fin k) z hz a, mul_zero]

/-- **A vector killed by all the rows and supported off `Set.range ι` is zero**, provided the
`ι`-columns of the rows form an invertible matrix.  Complex companion of
`Work.WilE3.Identity.Affine.tangentCoordInjective`. -/
theorem eq_zero_of_kernel_of_supported (L : Fin j → Fin k → ℂ) (ι : Fin j → Fin k)
    (hΔ : (Matrix.of fun a b => L a (ι b)).det ≠ 0) (v : Fin k → ℂ)
    (hv : ∀ a, ∑ i, v i * L a i = 0) (hvS : ∀ l, l ∉ Set.range ι → v l = 0) : v = 0 := by
  classical
  let M : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => L a (ι b)
  have hΔM : M.det ≠ 0 := hΔ
  have hι : Function.Injective ι := by
    intro b1 b2 hb
    by_contra hne
    exact hΔM (Matrix.det_zero_of_column_eq (M := M) hne fun c => by
      show M c b1 = M c b2
      simp only [M, Matrix.of_apply, hb])
  let w : Fin j → ℂ := fun b => v (ι b)
  have hMw : M.mulVec w = 0 := by
    funext a
    have hkey : ∑ b : Fin j, L a (ι b) * v (ι b) = ∑ i, v i * L a i := by
      calc ∑ b : Fin j, L a (ι b) * v (ι b)
          = ∑ i ∈ Finset.univ.image ι, L a i * v i := by
            rw [Finset.sum_image]
            intro x _ y _ hxy
            exact hι hxy
        _ = ∑ i, L a i * v i :=
            Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
              have hri : i ∉ Set.range ι := by
                rintro ⟨b, hb⟩
                exact hi (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩)
              rw [hvS i hri, mul_zero]
        _ = ∑ i, v i * L a i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, w, Pi.zero_apply]
    rw [hkey, hv a]
  have hw : w = 0 := by
    have hMinj : Function.Injective M.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det M, isUnit_iff_ne_zero]
      exact hΔM
    refine hMinj ?_
    rw [hMw, Matrix.mulVec_zero]
  funext i
  by_cases hi : i ∈ Set.range ι
  · obtain ⟨b, hb⟩ := hi
    rw [← hb]
    exact congrFun hw b
  · exact hvS i hi

/-! ## §2. The common kernel is the span of the frame -/

/-- **The common kernel of the `h`-rows is spanned by the tangential frame.**  For an injective `ι`
and at a point `z` where the `ι`-Jacobian `Δ = jacValC c h ι z` does not vanish, the vectors
`v` killed by all the row functionals `w ↦ Σ i, w i * (∂_i h_a)(z)` are exactly the linear
combinations of the `k - j` tangential frame vectors `VcoefC c h ι l z` (`l ∉ Set.range ι`).

Proof sketch: the `j × k` matrix `(∂_i h_a)(z)` has rank `j` (its `ι`-columns form the invertible
`jacMatC`), so its kernel has dimension `k - j`; the `V_l` (`l ∉ range ι`) lie in the kernel
(`VcoefC_tangent`) and are linearly independent (for `i ∉ range ι` one has
`VcoefC c h ι l z i = if i = l then 1 else 0`, since no `ι b` equals such an `i`); a dimension count
(or directly: subtracting `Σ_l v_l • V_l` leaves a vector supported on the `ι`-columns, which lies in
the kernel only if it is zero) gives the equality. -/
theorem kernel_frame_rows {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (hι : Function.Injective ι)
    (z : Fin k → ℂ) (hz : Work.WilE3.Frame.jacValC c h ι z ≠ 0) (v : Fin k → ℂ) :
    (∀ a, ∑ i, v i * Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c i (h a)) z = 0) ↔
      ∃ c' : Work.WilE3.Frame.U k ι → ℂ,
        v = ∑ l : Work.WilE3.Frame.U k ι, c' l • Work.WilE3.Frame.VcoefC c h ι l z := by
  classical
  have hΔ : (Matrix.of fun a b => eaEvalC c (eaD c (ι b) (h a)) z).det ≠ 0 := by
    have h1 : (Matrix.of fun a b => eaEvalC c (eaD c (ι b) (h a)) z).det = jacValC c h ι z :=
      (jacValC_eq_det c h ι z).symm
    rw [h1]
    exact hz
  constructor
  · intro hv
    refine ⟨fun l => v l.1, ?_⟩
    show v = ∑ l : U k ι, v l.1 • VcoefC c h ι l z
    have hTval : ∀ i : Fin k, i ∉ Set.range ι →
        (∑ l : U k ι, v l.1 • VcoefC c h ι l z) i = v i := by
      intro i hi
      simpa using sum_coeff_mul_VcoefC_of_notMem_range c h ι z (fun l => v l.1) i hi
    have hTker : ∀ a, ∑ i, (∑ l : U k ι, v l.1 • VcoefC c h ι l z) i *
        eaEvalC c (eaD c i (h a)) z = 0 :=
      fun a => sum_span_VcoefC_mul c h ι z hz (fun l => v l.1) a
    have hwker : ∀ a, ∑ i, (v - ∑ l : U k ι, v l.1 • VcoefC c h ι l z) i *
        eaEvalC c (eaD c i (h a)) z = 0 := by
      intro a
      have h1 : ∀ i : Fin k, (v - ∑ l : U k ι, v l.1 • VcoefC c h ι l z) i *
            eaEvalC c (eaD c i (h a)) z
          = v i * eaEvalC c (eaD c i (h a)) z
            - (∑ l : U k ι, v l.1 • VcoefC c h ι l z) i * eaEvalC c (eaD c i (h a)) z := by
        intro i
        rw [Pi.sub_apply]
        ring
      have hsum_eq : (∑ i, (v - ∑ l : U k ι, v l.1 • VcoefC c h ι l z) i *
            eaEvalC c (eaD c i (h a)) z)
          = ∑ i, (v i * eaEvalC c (eaD c i (h a)) z
              - (∑ l : U k ι, v l.1 • VcoefC c h ι l z) i * eaEvalC c (eaD c i (h a)) z) :=
        Finset.sum_congr rfl fun i _ => h1 i
      rw [hsum_eq, Finset.sum_sub_distrib, hv a, hTker a, sub_self]
    have hwsup : ∀ i : Fin k, i ∉ Set.range ι →
        (v - ∑ l : U k ι, v l.1 • VcoefC c h ι l z) i = 0 := by
      intro i hi
      rw [Pi.sub_apply, hTval i hi, sub_self]
    have hw0 : v - ∑ l : U k ι, v l.1 • VcoefC c h ι l z = 0 :=
      eq_zero_of_kernel_of_supported (fun a i => eaEvalC c (eaD c i (h a)) z) ι hΔ _
        hwker hwsup
    exact sub_eq_zero.mp hw0
  · rintro ⟨c', hc'⟩
    intro a
    rw [hc']
    exact sum_span_VcoefC_mul c h ι z hz c' a

end

end Work.WilE3.Frame

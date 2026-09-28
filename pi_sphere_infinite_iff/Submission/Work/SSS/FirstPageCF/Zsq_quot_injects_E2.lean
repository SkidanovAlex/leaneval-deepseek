import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FirstPage.HomElts
import Submission.Work.SSS.FirstPageCF.ZsqElts
import Submission.Work.SSS.FirstPageCF.mem_Bsq_of_psi_mem_range

namespace Work.SSS.FirstPageCF

open CategoryTheory CategoryTheory.Limits

attribute [-instance] AddCommGroup.toIntModule

/-- **The general form of `Zsq_quot_injects_E2`.**  For `2 ≤ s` and `n = s + t`, the model
`Zsq ξ s n ⧸ BsqZ ξ s n` of the `(s,t)`-term of the second page injects into `E2 ξ s t`. -/
theorem Zsq_quot_injects_E2_gen {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C)
    (s n t : ℕ) (hst : n = s + t) (hs : 2 ≤ s) :
    ∃ f : (↥(Zsq ξ s n) ⧸ BsqZ ξ s n) →ₗ[ℤ] (E2 ξ s t), Function.Injective f := by
  subst hst
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  -- the short complex computing `E²_{k+2,t}`
  let S₂ := (E1Complex ξ t).sc' (k+3) (k+2) (k+1)
  have hS₂g : S₂.g.hom = (d1 ξ (k+1) t).hom := by
    rw [show S₂.g = (E1Complex ξ t).d (k+2) (k+1) from rfl]
    exact congrArg ModuleCat.Hom.hom (E1Complex_d ξ t (k+1))
  have hS₂f : S₂.f.hom = (d1 ξ (k+2) t).hom := by
    rw [show S₂.f = (E1Complex ξ t).d (k+3) (k+2) from rfl]
    exact congrArg ModuleCat.Hom.hom (E1Complex_d ξ t (k+2))
  -- the class map restricted to the cycles of the row complex
  let ψc : ↥(Zsq ξ (k+2) ((k+2)+t)) →ₗ[ℤ] ↥(LinearMap.ker S₂.g.hom) :=
    (psi ξ (k+2) t (by omega)).codRestrict _ (fun z => d1_sc_psi ξ k t z)
  let ψq : ↥(Zsq ξ (k+2) ((k+2)+t)) →ₗ[ℤ] S₂.moduleCatLeftHomologyData.H :=
    (Submodule.mkQ (LinearMap.range S₂.moduleCatToCycles)).comp ψc
  -- the class of a `Bsq`-element is the class of an `im (d¹)`-element
  have hbot : BsqZ ξ (k+2) ((k+2)+t) ≤ ψq.ker := by
    intro z hz
    have hz' : (z : (grF ξ.F (k+2)).X ((k+2)+t)) ∈ Bsq ξ (k+2) ((k+2)+t) := hz
    have hin : psi ξ (k+2) t (by omega) z ∈ LinearMap.range S₂.f.hom := by
      rw [hS₂f]
      exact Bsq_le_psi_range ξ k t z hz'
    obtain ⟨w, hw⟩ := hin
    have hmem : ψc z ∈ LinearMap.range S₂.moduleCatToCycles := by
      rw [LinearMap.mem_range]
      refine ⟨w, ?_⟩
      apply Subtype.ext
      rw [moduleCatToCycles_val_C]
      exact hw
    show ψq z = 0
    exact (Submodule.Quotient.eq (p := LinearMap.range S₂.moduleCatToCycles)).mpr
      (by simpa using hmem)
  -- conversely, an element killed by the class map lies in `Bsq`
  have hker : ψq.ker ≤ BsqZ ξ (k+2) ((k+2)+t) := by
    intro z hz
    have hz0 : (Submodule.mkQ (LinearMap.range S₂.moduleCatToCycles)) (ψc z) = 0 := hz
    have hz0' : Submodule.Quotient.mk (ψc z)
        = Submodule.Quotient.mk (0 : ↥(S₂.g.hom).ker) := hz0
    have hmem : ψc z ∈ LinearMap.range S₂.moduleCatToCycles := by
      have h1 := (Submodule.Quotient.eq (p := LinearMap.range S₂.moduleCatToCycles)).mp hz0'
      simpa using h1
    rw [LinearMap.mem_range] at hmem
    obtain ⟨u, hu⟩ := hmem
    have hu' : S₂.f.hom u = psi ξ (k+2) t (by omega) z := by
      have h1 := congrArg (Subtype.val) hu
      rw [moduleCatToCycles_val_C] at h1
      exact h1
    have hv : psi ξ (k+2) t (by omega) z ∈ LinearMap.range S₂.f.hom := ⟨u, hu'⟩
    rw [hS₂f] at hv
    exact mem_Bsq_of_psi_mem_range ξ k t z (by rw [hS₂f]; exact hv)
  let ψL : ↥(Zsq ξ (k+2) ((k+2)+t)) ⧸ BsqZ ξ (k+2) ((k+2)+t) →ₗ[ℤ]
      S₂.moduleCatLeftHomologyData.H :=
    Submodule.liftQ (BsqZ ξ (k+2) ((k+2)+t)) (f := ψq) hbot
  let e₂ := (S₂.moduleCatHomologyIso.inv) ≫
      ((E1Complex ξ t).homologyIsoSc' (k+3) (k+2) (k+1)
        (prev_down_eq_succ (k+2)) (next_down_eq_pred (k+2))).inv
  refine ⟨e₂.hom.comp ψL, ?_⟩
  have hinj1 : Function.Injective ψL := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hinj2 : Function.Injective (S₂.moduleCatHomologyIso.inv.hom) :=
    (ModuleCat.mono_iff_injective S₂.moduleCatHomologyIso.inv).mp inferInstance
  have hinj3 : Function.Injective
      (((E1Complex ξ t).homologyIsoSc' (k+3) (k+2) (k+1)
        (prev_down_eq_succ (k+2)) (next_down_eq_pred (k+2))).inv.hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact (hinj3.comp hinj2).comp hinj1

/-- **The first-page model of `E²`.**  For `2 ≤ s ≤ n`, the standard model of the `E²` term
`E2 ξ s (n-s)` — the relative `n`-cycles of `F_s` whose boundary lifts to `F_{s-2}`, modulo the
boundaries coming from `F_{s+1}` (the submodules `Work.SSS.Zsq` and `Work.SSS.Bsq` of
`(F_s/F_{s-1})_n`, see `Submission/Work/SSS/FibreColDefs.lean`) — embeds into `E2 ξ s (n-s)`.

Roadmap.  An element of `Zsq` is the class in `(F_s/F_{s-1})_n` of some `x ∈ F_s.X n` with `d x`
in the image of `F_{s-2}`.  Since `F_{s-2} ⊆ F_{s-1}`, the image of `x` in the graded piece is a
cycle, so it has a class `[x] ∈ E1 ξ s (n-s) = (grF ξ.F s).homology n`; then
* `d1 ξ (s-1) (n-s) [x] = 0`: use `d1 = kF ≫ jF`, `ShortComplex.ShortExact.δ_eq` for `kF` (the
  class of the boundary of a lift) and the fact that the composite chain map
  `F_{s-2} → F_{s-1} → grF ξ (s-1)` is zero for `jF`;
* the resulting map `Zsq → ker (d1 ξ (s-1) (n-s))` kills `Bsq`: an element `d y` with
  `y ∈ F_{s+1}.X (n+1)`, `d y ∈ F_s.X n` has class `d1 ξ s (n-s) [y]`;
* it is injective modulo the image of `d1 ξ s (n-s)`: if the class of `x` equals `jF w` with
  `w ∈ ker (homologyMap (incF ξ.F s) n)`, then `w = [c]` for an `n`-cycle `c ∈ F_s.X n` which is a
  boundary `c = d e` in `F_{s+1}`, and `[x] = [c]` in the graded piece gives
  `x = d (e + f) + z` with `f ∈ F_s.X (n+1)`, `z ∈ F_{s-1}.X n`, i.e. `x ∈ Bsq`.
Conclude with the first isomorphism theorem.  Only the existence of an injection is needed. -/
theorem Zsq_quot_injects_E2 {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (s n : ℕ)
    (hs : 2 ≤ s) (hsn : s ≤ n) :
    ∃ f : (↥(Zsq ξ s n) ⧸ BsqZ ξ s n) →ₗ[ℤ] (E2 ξ s (n - s)), Function.Injective f :=
  Zsq_quot_injects_E2_gen ξ s n (n - s) (Nat.add_sub_cancel' hsn).symm hs

end Work.SSS.FirstPageCF

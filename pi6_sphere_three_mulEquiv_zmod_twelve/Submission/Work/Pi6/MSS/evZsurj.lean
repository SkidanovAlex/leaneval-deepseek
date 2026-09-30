import Mathlib
import Submission.Work.Pi6.MSS.evSaux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Surjectivity of `evZ`

`evZ : Z_1^{s,n} ⟶ Hom_𝕜(H_n(gr_s), 𝕜)` evaluates a cochain `x ∈ F^s C^n` with `dx ∈ F^{s+1}C^{n+1}`
on the cycles of the graded piece `gr_s` of the Serre chain filtration of `p : E → B`.

Over a field this map is *surjective*: given a functional `ψ` on `H_n(gr_s)`, choose a linear
retraction `ρ` of the cycles of `gr_s` onto themselves; then `q := ψ ∘ mkQ ∘ ρ` is a functional on
all of `(gr_s)_n` which kills boundaries.  By `evTheta_surj` there is `x ∈ F^s C^n` with
`x(incl (grSecX z)) = q z` for all cycles `z`; the chain-level computation
`x(incl w) = q (grPi w)` for `w ∈ C_{n+1}(A_{s+1})` (split along `exists_eq_sec_add`, and using that
`grPi` commutes with the differential) shows `dx` vanishes on `C_{n+1}(A_{s+1})`, i.e. `x ∈ Z_1^s`.
On cycles `x` then represents `ψ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem evZsurj (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.Pi6.MSS.sF p) s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex (Work.Pi6.MSS.sF p) s) n) :
    Function.Surjective (Work.Pi6.MSS.evZ 𝕜 p s n hann) := by
  intro ψ
  -- a linear retraction of the cycles of the graded piece onto themselves
  obtain ⟨ρ, hρ⟩ := Work.StemsB.exists_retraction_subspace_field 𝕜
    (Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n)
  -- the functional on the cycles, extended to all chains
  let q : ↥((Kg 𝕜 p s).X n) →ₗ[𝕜] 𝕜 :=
    ψ.comp ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ.comp ρ)
  -- it is realised by a cochain of `F^s`
  obtain ⟨x, hx⟩ := evTheta_surj 𝕜 p s n hann q
  have hxq : ∀ z : ↥((Kg 𝕜 p s).X n),
      cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) = q z := by
    intro z
    have h := LinearMap.congr_fun hx z
    rwa [evTheta_apply] at h
  -- `q` kills boundaries
  have hqkill : ∀ y : ↥((Kg 𝕜 p s).X (n+1)), q (((Kg 𝕜 p s).d (n+1) n).hom y) = 0 := by
    intro y
    change ψ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ
      (ρ (((Kg 𝕜 p s).d (n+1) n).hom y))) = 0
    have hy : ((Kg 𝕜 p s).d (n+1) n).hom y ∈ Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n :=
      Work.StemsB.fdB_le_fdZ 𝕜 (Kg 𝕜 p s) n ⟨y, rfl⟩
    have hρy : ρ (((Kg 𝕜 p s).d (n+1) n).hom y) = ⟨_, hy⟩ := by
      have h := congrArg (fun (φ : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n) →ₗ[𝕜]
          ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n)) => φ ⟨_, hy⟩) hρ
      simpa using h
    rw [hρy]
    have hmem : (⟨_, hy⟩ : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n)) ∈
        Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n :=
      (Work.StemsB.mem_fdH 𝕜 (Kg 𝕜 p s) n _).mpr ⟨y, rfl⟩
    rw [show (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ
        (⟨_, hy⟩ : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n)) = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hmem]
    exact map_zero ψ
  -- the coboundary of `x` lies in `F^{s+1}`
  have hdF : (Wc 𝕜 p).d n x.1 ∈ (Wc 𝕜 p).F (s+1) (n+1) := by
    rw [mem_F_iff 𝕜 p (s+1) (n+1) hann]
    intro z
    -- move the differential to the other side and use that `inclL` is a chain map
    have hchain : ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom
        (((inclL 𝕜 p (s+1)).f (n+1)).hom z) =
        ((inclL 𝕜 p (s+1)).f n).hom (((Cc 𝕜 p (s+1)).d (n+1) n).hom z) := by
      have h := congrArg (fun (g : (Cc 𝕜 p (s+1)).X (n+1) ⟶
          (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n) => g.hom z)
          (inclL_d 𝕜 p (s+1) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearMap.comp_apply] at h
      exact h
    rw [← Wc_d_apply_applied 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f (n+1)).hom z), hchain]
    -- split the chain of `A_{s+1}` along the chosen section of the graded piece
    obtain ⟨b, hb⟩ := exists_eq_sec_add 𝕜 p s n (((Cc 𝕜 p (s+1)).d (n+1) n).hom z)
    rw [hb, map_add, map_add, hxq, kills_grIncl 𝕜 p s n hann x.1 x.2 b, add_zero]
    -- `grPi` commutes with the differential, so what is left is `q` of a boundary
    have hgr : grPi 𝕜 p s n (((Cc 𝕜 p (s+1)).d (n+1) n).hom z) =
        ((Kg 𝕜 p s).d (n+1) n).hom (((Kgπ 𝕜 p s).f (n+1)).hom z) := by
      have h := congrArg (fun (g : ((Work.SSSR.serF 𝕜 (sF p)).obj s).X (n+1) ⟶
          (Kg 𝕜 p s).X n) => g.hom z) (Kgπ_d 𝕜 p s n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearMap.comp_apply] at h
      exact h.symm
    rw [hgr]
    exact hqkill _
  -- `x` is a class of the first page representing `ψ`
  refine ⟨⟨x.1, (mem_pZ_one (Wc 𝕜 p) s n x.1).mpr ⟨x.2, hdF⟩⟩, ?_⟩
  apply LinearMap.ext
  intro w
  obtain ⟨z, rfl⟩ := (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ_surjective w
  rw [evZ_apply]
  rw [hxq (z : ↥((Kg 𝕜 p s).X n))]
  have hρz : ρ z = z := by
    have h := congrArg (fun (φ : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n) →ₗ[𝕜]
        ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n)) => φ z) hρ
    simpa using h
  have hqz : q z = ψ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ z) := by
    change ψ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ (ρ z)) =
      ψ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ z)
    rw [hρz]
  exact hqz

end

end Work.Pi6.MSS

import Mathlib
import Submission.Work.Tower.ProPEndgame.Defs
import Submission.Work.GolodShafarevich.Setup
import Submission.Work.GolodShafarevich.RelationModule.ker_psi_eq_span

namespace Work.Tower.ProPEndgame

/-- For a presentation `φ : F_d ↠ G` of a finite group, the relation module
`ker (ψ : 𝔽_p[G]^d → 𝔽_p[G])`, `ψ x = ∑ᵢ xᵢ (φ xᵢ - 1)`, is spanned as an `𝔽_p[G]`-module by the
Fox derivative vectors `Vfun φ r` of *all* elements `r ∈ ker φ`.

Proof.  `⊆`: `psi_Vfun` gives `ψ (Vfun φ w) = of (φ w) - 1 = 0` for `w ∈ ker φ`.  `⊇`: since `G` is
finite, `ker φ` has finite index in the finitely generated free group `F_d`, hence is finitely
generated (Schreier); being normal, it is the normal closure of a finite set `{Rⱼ}`, and
`Work.GolodShafarevich.RelationModule.ker_psi_eq_span` identifies `ker ψ` with the span of the
`Vfun φ Rⱼ`.  Each `Rⱼ ∈ ker φ`, so this span is contained in the span of *all* `Vfun φ r`. -/
theorem ker_psi_span_all (p : ℕ) [Fact p.Prime] {d : ℕ} {G : Type} [Group G] [Finite G]
    (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ) :
    Submodule.span (MonoidAlgebra (ZMod p) G)
        (Set.range (fun r : φ.ker =>
          Work.GolodShafarevich.Vfun (ZMod p) φ (r : FreeGroup (Fin d)))) =
      LinearMap.ker (Work.GolodShafarevich.psi (ZMod p) φ) := by
  refine le_antisymm ?_ ?_
  · -- `⊆`: `ψ (Vfun φ r) = of (φ r) - 1 = 0` for `r ∈ ker φ`.
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Work.GolodShafarevich.psi_Vfun,
      show φ (r : FreeGroup (Fin d)) = 1 from MonoidHom.mem_ker.mp r.2, map_one, sub_self]
  · -- `⊇`: lift `x` to `k[F_d]^d`, use that `ker (groupAlgMap φ)` is spanned by `of n - 1`
    -- (`n ∈ ker φ`), and push forward along `groupAlgMap φ`, using `Vfun φ n = φ_* Vfun id n`.
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hsurj : ∀ i : Fin d, ∃ a : MonoidAlgebra (ZMod p) (FreeGroup (Fin d)),
        Work.GolodShafarevich.groupAlgMap (ZMod p) φ a = x i :=
      fun i => Work.GolodShafarevich.RelationModule.groupAlgMap_surjective φ hφ (x i)
    choose xt hxt using hsurj
    have hbker : Work.GolodShafarevich.psi (ZMod p) (MonoidHom.id (FreeGroup (Fin d))) xt ∈
        RingHom.ker (Work.GolodShafarevich.groupAlgMap (ZMod p) φ) := by
      rw [RingHom.mem_ker, Work.GolodShafarevich.RelationModule.groupAlgMap_psi_id,
        show (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ (xt i)) = x from funext hxt,
        hx]
    rw [Work.GolodShafarevich.RelationModule.ker_groupAlgMap] at hbker
    set P : Submodule (MonoidAlgebra (ZMod p) (FreeGroup (Fin d)))
        (Fin d → MonoidAlgebra (ZMod p) (FreeGroup (Fin d))) :=
      Submodule.span (MonoidAlgebra (ZMod p) (FreeGroup (Fin d)))
        (Set.range (fun n : φ.ker =>
          Work.GolodShafarevich.Vfun (ZMod p) (MonoidHom.id (FreeGroup (Fin d)))
            (n : FreeGroup (Fin d)))) with hP
    have hle : Submodule.span (MonoidAlgebra (ZMod p) (FreeGroup (Fin d)))
        (Set.range (fun n : φ.ker =>
          MonoidAlgebra.of (ZMod p) (FreeGroup (Fin d)) (n : FreeGroup (Fin d)) - 1)) ≤
        Submodule.map (Work.GolodShafarevich.psi (ZMod p) (MonoidHom.id (FreeGroup (Fin d))))
          P := by
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      refine Submodule.mem_map.mpr
        ⟨Work.GolodShafarevich.Vfun (ZMod p) (MonoidHom.id (FreeGroup (Fin d)))
            (n : FreeGroup (Fin d)), Submodule.subset_span ⟨n, rfl⟩, ?_⟩
      rw [Work.GolodShafarevich.psi_Vfun]
      rfl
    obtain ⟨y, hyP, hyb⟩ := Submodule.mem_map.mp (hle hbker)
    have hyx : y = xt := Work.GolodShafarevich.RelationModule.psi_id_injective hyb
    have hxtP : xt ∈ P := hyx ▸ hyP
    have hmain : ∀ z ∈ P,
        (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ (z i)) ∈
          Submodule.span (MonoidAlgebra (ZMod p) G) (Set.range (fun r : φ.ker =>
            Work.GolodShafarevich.Vfun (ZMod p) φ (r : FreeGroup (Fin d)))) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨n, rfl⟩ := hv
        rw [← Work.GolodShafarevich.RelationModule.Vfun_eq_mapDomain_id]
        exact Submodule.subset_span ⟨n, rfl⟩
      | zero =>
        have h0 : (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ
            ((0 : Fin d → MonoidAlgebra (ZMod p) (FreeGroup (Fin d))) i)) = 0 := by
          ext i
          simp
        rw [h0]
        exact Submodule.zero_mem _
      | add a b _ _ iha ihb =>
        have h : (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ ((a + b) i)) =
            (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ (a i)) +
              (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ (b i)) := by
          ext i
          simp [Pi.add_apply]
        rw [h]
        exact Submodule.add_mem _ iha ihb
      | smul c a _ iha =>
        have h : (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ ((c • a) i)) =
            (Work.GolodShafarevich.groupAlgMap (ZMod p) φ c) •
              (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ (a i)) := by
          ext i
          simp [Pi.smul_apply, smul_eq_mul]
        rw [h]
        exact Submodule.smul_mem _ _ iha
    rw [show x = (fun i => Work.GolodShafarevich.groupAlgMap (ZMod p) φ (xt i)) from
      funext (fun i => (hxt i).symm)]
    exact hmain xt hxtP

end Work.Tower.ProPEndgame

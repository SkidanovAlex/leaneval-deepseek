import Mathlib
import Submission.Work.Drive.Push.spineAlignment
import Submission.Work.Drive.Push.flattenAlignedSpine
import Submission.Work.Drive.Whitney.modelChart
import Submission.Work.Whitney.CutPush.exists_collar_trivialisation
import Submission.Work.Drive.Whitney.linearEquivMap_inf_bot
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Drive.PushDisc.sheetOneTubeFlattening

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

/-!
# The flattening data of the first sheet of the Whitney bigon

`Work.Drive.PushDisc.sheetOneFlatteningData` is step (O1) of the asymmetric normal form
(`Submission/Work/Drive/NOTES_DISC_S73_asymmetric.md` §5): it flattens the *first* sheet of a bigon
along the arc `γ₁` inside the clean region `W`, and pins the two double points `p₁`, `q₁` of that
arc to the two model double points `(-1, 0, 0, 0)` and `(1, 0, 0, 0)` of the model space
`Work.Drive.Whitney.Mdl k`.

The proof is an assembly of two halves:

* `Work.Drive.PushDisc.sheetOneTubeFlattening` (the tube flattening: an open tube `U` around `γ₁`
  with `closure U ⊆ W`, `p₂, q₂ ∉ U`, and a global `C^∞` diffeomorphism `A` with `A (f x) ∈ K` for
  all `x ∈ U`, `finrank K = n`) — note that `A (f x) ∈ K` extends to the *closure* of `U` because
  `K` is closed (finite-dimensional) and `A ∘ f` is continuous;
* `Work.Drive.PushDisc.exists_linearEquiv_sheetA` (the linear core below): an isomorphism
  `L : ℝ^{2n} ≃ₗ Mdl k` carrying `K` onto the model plane `sheetA` and a prescribed vector
  `d ∈ K \ {0}` to `(2, 0, 0, 0) ∈ sheetA`.

The identification `Φ := L (A · + w)` — with `w ∈ K` the translate that puts `A (f p₁)` at
`(-1, 0, 0, 0)` — is then an affine isomorphism of `ℝ^{2n}` onto the model (so `Θ := Φ⁻¹` is
smooth), it maps `f '' closure U` into `sheetA`, and it maps `f p₁`, `f q₁` to `(-1,0,0,0)`,
`(1,0,0,0)` because `A (f q₁) - A (f p₁) = d` is carried to `(2,0,0,0)`.
-/

/-- **The linear core of the sheet-one flattening.**  For an `n`-plane `K` of `ℝ^{2n}` (`n = k+1`),
a nonzero vector `d ∈ K` and the point `(2,0,0,0)` of the model plane `sheetA` there is a linear
equivalence `L : ℝ^{2n} ≃ₗ Mdl k` and an isomorphism `e : K ≃ₗ sheetASub k` of the plane with the
model plane such that `L` restricts to `e` on `K` and `e d = (2, 0, 0, 0)`.

(Correspondingly `L` carries `K` *onto* `sheetA`, and `L d = (2,0,0,0)`.) -/
theorem exists_linearEquiv_sheetA {n k : ℕ} (hk : n = k + 1)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (hK : Module.finrank ℝ K = n)
    (d : EuclideanSpace ℝ (Fin (2 * n))) (hd : d ∈ K) (hd0 : d ≠ 0) :
    ∃ (L : EuclideanSpace ℝ (Fin (2 * n)) ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k)
      (e : ↥K ≃ₗ[ℝ] sheetASub k),
      (∀ y : ↥K, L (y : EuclideanSpace ℝ (Fin (2 * n))) = (e y : Work.Drive.Whitney.Mdl k)) ∧
      e ⟨d, hd⟩ = ⟨((2 : ℝ), 0, 0, 0), ⟨rfl, rfl⟩⟩ := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hMdl : Module.finrank ℝ (Work.Drive.Whitney.Mdl k) = 2 * n := by
    rw [finrank_Mdl, hk]
  -- transport `sheetA` into `ℝ^{2n}` by an arbitrary linear equivalence
  let j : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hMdl, hE])
  set S : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    Submodule.map j.toLinearMap (sheetASub k) with hS
  have hSfin : Module.finrank ℝ S = n := by
    rw [hS, ← (j.submoduleMap (sheetASub k)).finrank_eq, finrank_sheetASub, hk]
  have hzmem : ((2 : ℝ), 0, 0, 0) ∈ sheetASub k := ⟨rfl, rfl⟩
  have hzne : ((2 : ℝ), 0, 0, 0) ≠ (0 : Work.Drive.Whitney.Mdl k) := by
    intro h
    have h2 : (2 : ℝ) = 0 := congrArg (fun z : Work.Drive.Whitney.Mdl k => z.1) h
    norm_num at h2
  have hzSmem : j ((2 : ℝ), 0, 0, 0) ∈ S := Submodule.mem_map.mpr ⟨_, hzmem, rfl⟩
  have hzSne : j ((2 : ℝ), 0, 0, 0) ≠ 0 := by
    intro h
    exact hzne (j.injective (h.trans (map_zero j).symm))
  obtain ⟨e₀, he₀⟩ := Work.Drive.Whitney.exists_linearEquiv_map_eq (T := K) (S := S)
    hd hzSmem hd0 hzSne (by rw [hK, hSfin])
  let e : ↥K ≃ₗ[ℝ] sheetASub k := e₀.trans (j.submoduleMap (sheetASub k)).symm
  have he : e ⟨d, hd⟩ = ⟨((2 : ℝ), 0, 0, 0), hzmem⟩ := by
    show (j.submoduleMap (sheetASub k)).symm (e₀ ⟨d, hd⟩) = ⟨((2 : ℝ), 0, 0, 0), hzmem⟩
    rw [he₀]
    apply Subtype.ext
    rw [LinearEquiv.submoduleMap_symm_apply]
    exact LinearEquiv.symm_apply_apply j ((2 : ℝ), 0, 0, 0)
  -- extend along complements
  obtain ⟨N₁, hN₁⟩ := Submodule.exists_isCompl K
  obtain ⟨N₂, hN₂⟩ := Submodule.exists_isCompl (sheetASub k)
  have hdim : Module.finrank ℝ N₁ = Module.finrank ℝ N₂ := by
    have h1 : Module.finrank ℝ K + Module.finrank ℝ N₁
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
      have h := (Submodule.finrank_sup_add_finrank_inf_eq K N₁).symm
      rw [hN₁.sup_eq_top, hN₁.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h
      exact h
    have h2 : Module.finrank ℝ (sheetASub k) + Module.finrank ℝ N₂
        = Module.finrank ℝ (Work.Drive.Whitney.Mdl k) := by
      have h := (Submodule.finrank_sup_add_finrank_inf_eq (sheetASub k) N₂).symm
      rw [hN₂.sup_eq_top, hN₂.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h
      exact h
    rw [hE, hK] at h1
    rw [hMdl, finrank_sheetASub] at h2
    omega
  refine ⟨(Submodule.prodEquivOfIsCompl K N₁ hN₁).symm.trans
      ((e.prodCongr (LinearEquiv.ofFinrankEq N₁ N₂ hdim)).trans
        (Submodule.prodEquivOfIsCompl (sheetASub k) N₂ hN₂)), e, ?_, he⟩
  intro y
  show (Submodule.prodEquivOfIsCompl (sheetASub k) N₂ hN₂)
      ((e.prodCongr (LinearEquiv.ofFinrankEq N₁ N₂ hdim))
        ((Submodule.prodEquivOfIsCompl K N₁ hN₁).symm (y : EuclideanSpace ℝ (Fin (2 * n)))))
    = (e y : Work.Drive.Whitney.Mdl k)
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left K N₁ hN₁ y]
  show (↑((Submodule.prodEquivOfIsCompl (sheetASub k) N₂ hN₂)
      ((e.prodCongr (LinearEquiv.ofFinrankEq N₁ N₂ hdim)) (y, 0))) : Work.Drive.Whitney.Mdl k)
    = (e y : Work.Drive.Whitney.Mdl k)
  rw [LinearEquiv.prodCongr_apply, map_zero, Submodule.coe_prodEquivOfIsCompl']
  simp


/-- **The flattening data of the first sheet along the arc `γ₁`.**  From the tube flattening of
`γ₁` (`sheetOneTubeFlattening`) and the linear algebra of `exists_linearEquiv_sheetA`, the sheet
`f '' U` is carried into the model plane `sheetA` by a global `C^∞` diffeomorphism `Φ` with inverse
`Θ`, with the two double points `p₁`, `q₁` mapped to `(-1, 0, 0, 0)` and `(1, 0, 0, 0)`. -/
theorem sheetOneFlatteningData {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂)
    (hfp : f p₁ = f p₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (_hk : n = k + 1)
      (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
      (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))) (U : Set M),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y) ∧
      (∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ) ∧
      IsOpen U ∧ closure U ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ p₂ ∉ U ∧ q₂ ∉ U ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) ∧
      (∀ x : M, x ∈ closure U → Φ (f x) ∈ Work.Drive.Whitney.sheetA) ∧
      Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) ∧ Φ (f q₁) = ((1 : ℝ), 0, 0, 0) := by
  classical
  obtain ⟨U, A, Ainv, K, hUo, hUcl, hUarc, hp₂U, hq₂U, hA, hAinv, hAl, hAr, hKfin, hAK⟩ :=
    sheetOneTubeFlattening hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₃ hp₁p₂ hfp hclean hsep
      γ₁ hγ₁ hγ₁0 hγ₁1 hγW₁ hγ₁inj hγ₁smooth hγ₁imm hp₂arc hq₂arc
  -- the two endpoints of the arc lie in `U`
  have hp₁U : p₁ ∈ U := hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0⟩
  have hq₁U : q₁ ∈ U := hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1⟩
  -- the two double points have different images
  have hfne : f p₁ ≠ f q₁ := by
    intro h
    rcases hclean p₁ q₁ hW₁ hW₃ h with h1 | h1 | h1 | h1 | h1
    · have h10 : (0 : ℝ) = 1 :=
        hγ₁inj (by norm_num) (by norm_num) (by rw [hγ₁0, hγ₁1, h1])
      norm_num at h10
    · exact hp₂arc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1.trans h1.2⟩
    · exact absurd h1.1 hp₁p₂
    · have h10 : (0 : ℝ) = 1 :=
        hγ₁inj (by norm_num) (by norm_num) (by rw [hγ₁0, hγ₁1, h1.1])
      norm_num at h10
    · exact hq₂arc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0.trans h1.1⟩
  have hd0 : A (f q₁) - A (f p₁) ≠ 0 := by
    intro h
    exact hfne (hAl.injective (sub_eq_zero.mp h)).symm
  have hdK : A (f q₁) - A (f p₁) ∈ K := K.sub_mem (hAK q₁ hq₁U) (hAK p₁ hp₁U)
  -- the membership in `K` extends to the closure of `U`
  have hAcl : ∀ x : M, x ∈ closure U → A (f x) ∈ K := by
    intro x hx
    have hcont : Continuous (fun y : M => A (f y)) := hA.continuous.comp hf.continuous
    have hclosed : IsClosed (K : Set (EuclideanSpace ℝ (Fin (2 * n)))) :=
      Submodule.closed_of_finiteDimensional K
    have hsub : (fun y : M => A (f y)) '' closure U
        ⊆ (K : Set (EuclideanSpace ℝ (Fin (2 * n)))) :=
      (image_closure_subset_closure_image hcont).trans
        (closure_minimal (Set.image_subset_iff.mpr (fun y hy => hAK y hy)) hclosed)
    exact hsub ⟨x, hx, rfl⟩
  -- the linear algebra: an isomorphism of the ambient space onto the model, pinned on `K`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨L, e, hLval, hed⟩ :=
    exists_linearEquiv_sheetA hk K hKfin (A (f q₁) - A (f p₁)) hdK hd0
  -- the translation that puts the two double points at the two model double points
  set q₁c : Work.Drive.Whitney.Mdl k := ((-1 : ℝ), 0, 0, 0) with hq₁c
  have hq₁cmem : q₁c ∈ sheetASub k := ⟨rfl, rfl⟩
  set w : EuclideanSpace ℝ (Fin (2 * n)) :=
    ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) - A (f p₁) with hw
  have hwK : w ∈ K := by
    rw [hw]
    exact K.sub_mem (e.symm ⟨q₁c, hq₁cmem⟩).2 (hAK p₁ hp₁U)
  set Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k :=
    fun y => L (A y + w) with hΦ
  set Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun ξ => Ainv (L.symm ξ - w) with hΘ
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) => L (z + w)) :=
      ((L.toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] Work.Drive.Whitney.Mdl k)).contDiff.comp
        (contDiff_id.add contDiff_const)
    exact h1.comp hA
  have hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := by
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => L.symm ξ - w) :=
      ((L.symm.toContinuousLinearEquiv :
          Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).contDiff.sub
        contDiff_const
    exact hAinv.comp h2
  have hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y := by
    intro y
    show Ainv (L.symm (L (A y + w)) - w) = y
    rw [LinearEquiv.symm_apply_apply, add_sub_cancel_right]
    exact hAl y
  have hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ := by
    intro ξ
    show L (A (Ainv (L.symm ξ - w)) + w) = ξ
    rw [hAr (L.symm ξ - w), sub_add_cancel, LinearEquiv.apply_symm_apply]
  have hsheet : ∀ x : M, x ∈ closure U → Φ (f x) ∈ Work.Drive.Whitney.sheetA := by
    intro x hx
    have h1 : A (f x) ∈ K := hAcl x hx
    have h2 : A (f x) + w ∈ K := K.add_mem h1 hwK
    show L (A (f x) + w) ∈ Work.Drive.Whitney.sheetA
    rw [show L (A (f x) + w)
        = (e ⟨A (f x) + w, h2⟩ : Work.Drive.Whitney.Mdl k) from hLval ⟨A (f x) + w, h2⟩]
    exact (e ⟨A (f x) + w, h2⟩).2
  have hend₁ : Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) := by
    have hval : A (f p₁) + w
        = ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) := by
      rw [hw]; abel
    show L (A (f p₁) + w) = ((-1 : ℝ), 0, 0, 0)
    rw [hval]
    rw [show L ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
        = (e (e.symm ⟨q₁c, hq₁cmem⟩) : Work.Drive.Whitney.Mdl k) from
      hLval (e.symm ⟨q₁c, hq₁cmem⟩)]
    rw [LinearEquiv.apply_symm_apply]
  have hend₂ : Φ (f q₁) = ((1 : ℝ), 0, 0, 0) := by
    have hval : A (f q₁) + w
        = ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
          + (A (f q₁) - A (f p₁)) := by
      rw [hw]; abel
    show L (A (f q₁) + w) = ((1 : ℝ), 0, 0, 0)
    rw [hval]
    rw [show L (((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
          + (A (f q₁) - A (f p₁)))
        = (e (e.symm ⟨q₁c, hq₁cmem⟩ + ⟨A (f q₁) - A (f p₁), hdK⟩) :
            Work.Drive.Whitney.Mdl k) from
      hLval (e.symm ⟨q₁c, hq₁cmem⟩ + ⟨A (f q₁) - A (f p₁), hdK⟩)]
    rw [map_add, LinearEquiv.apply_symm_apply, hed]
    show ((-1 : ℝ), 0, 0, 0) + ((2 : ℝ), 0, 0, 0) = ((1 : ℝ), 0, 0, 0)
    refine mdl_ext ?_ ?_ ?_ ?_ <;> simp <;> norm_num
  exact ⟨k, hk, A, Ainv, K, Φ, Θ, U, hA, hAinv, hAl, hAr, hΦsm, hΘsm, hΘΦ, hΦΘ, hUo, hUcl,
    hUarc, hp₂U, hq₂U, hKfin, hAK, hsheet, hend₁, hend₂⟩

end Work.Drive.PushDisc

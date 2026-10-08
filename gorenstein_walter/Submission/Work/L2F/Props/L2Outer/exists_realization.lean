import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Aut.realize
import Submission.Work.AUTL2.Aut.centralizer
import Submission.Work.AUTL2.Aut.images
import Submission.Work.AUTL2.Aut.pglIndex
import Submission.Work.AUTL2.Normalizer.eq

open scoped MatrixGroups

namespace Work.L2F.Props.L2Outer

/-- `MulAut.congr` evaluated: `((MulAut.congr e) f) y = e (f (e.symm y))`. -/
theorem mulAut_congr_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H) (f : MulAut G)
    (y : H) : ((MulAut.congr e) f) y = e (f (e.symm y)) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]

/-- If two permutations of `ℙ¹(F)` conjugate the image of `PSL(2,F)` in the same way, they are
equal: their quotient centralizes `pslImage F`, and (for `F` a field) that centralizer is
trivial whenever the ambient group is the symmetric group on `ℙ¹(F)`.

This is the uniqueness that makes the realization `Work.AUTL2.Aut.realize` canonical. -/
theorem realize_unique (F : Type*) [Field F] [DecidableEq F]
    (hcent : Subgroup.centralizer (Work.AUTL2.pslImage F :
      Set (Equiv.Perm (Work.AUTL2.P1 F))) = ⊥)
    (π π' : Equiv.Perm (Work.AUTL2.P1 F))
    (h : ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      π * Work.AUTL2.pslHom F x * π⁻¹ = π' * Work.AUTL2.pslHom F x * π'⁻¹) :
    π = π' := by
  have hmem : π⁻¹ * π' ∈ Subgroup.centralizer (Work.AUTL2.pslImage F :
      Set (Equiv.Perm (Work.AUTL2.P1 F))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨x, rfl⟩
    have h1 : (π⁻¹ * π') * Work.AUTL2.pslHom F x * (π⁻¹ * π')⁻¹ =
        Work.AUTL2.pslHom F x := by
      rw [mul_inv_rev, inv_inv]
      calc (π⁻¹ * π') * Work.AUTL2.pslHom F x * (π'⁻¹ * π)
          = π⁻¹ * (π' * Work.AUTL2.pslHom F x * π'⁻¹) * π := by group
        _ = π⁻¹ * (π * Work.AUTL2.pslHom F x * π⁻¹) * π := by rw [h x]
        _ = Work.AUTL2.pslHom F x := by group
    calc Work.AUTL2.pslHom F x * (π⁻¹ * π')
        = ((π⁻¹ * π') * Work.AUTL2.pslHom F x * (π⁻¹ * π')⁻¹) * (π⁻¹ * π') := by
          rw [h1]
      _ = (π⁻¹ * π') * Work.AUTL2.pslHom F x := by group
  have h1 : π⁻¹ * π' = 1 := by
    have h2 := hmem
    rw [hcent] at h2
    exact Subgroup.mem_bot.mp h2
  have h3 : π' = π := by rw [← mul_inv_cancel_left π π', h1, mul_one]
  exact h3.symm

theorem exists_realization (p e : ℕ) [Fact p.Prime] [Fintype (GaloisField p e)]
    [DecidableEq (GaloisField p e)] (hp : Odd p) (hq : 5 ≤ p ^ e)
    (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) [L.Normal]
    (eiso : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :
    ∃ Φ : Q →* Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)),
      (∀ x : ↥L, Φ x = Work.AUTL2.pslHom (GaloisField p e) (eiso x)) ∧
      (∀ q : Q, Φ q ∈ Work.AUTL2.pgammaL (GaloisField p e)) ∧
      (∀ (q : Q) (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)),
        Φ q * Work.AUTL2.pslHom (GaloisField p e) x * (Φ q)⁻¹ =
          Work.AUTL2.pslHom (GaloisField p e)
            ((MulAut.congr eiso) (MulAut.conjNormal q) x)) ∧
      (∀ q : Q, Φ q = 1 ↔ q ∈ Subgroup.centralizer (L : Set Q)) := by
  classical
  have hcent : Subgroup.centralizer (Work.AUTL2.pslImage (GaloisField p e) :
      Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)))) = ⊥ :=
    Work.AUTL2.Aut.centralizer p e hp hq
  have hpslinj : Function.Injective (Work.AUTL2.pslHom (GaloisField p e)) :=
    Work.AUTL2.Aut.pslHomInjective _
  -- The conjugation action of `Q` on `L ⊴ Q`, transported to `PSL(2, q)` through `eiso`.
  let α : Q →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :=
    (MulAut.congr eiso).toMonoidHom.comp (MulAut.conjNormal (H := L))
  have hαdef : ∀ q : Q, α q = (MulAut.congr eiso) (MulAut.conjNormal (H := L) q) := fun q => rfl
  -- Every such automorphism is realized by a permutation in `PΓL(2, q)`.
  have hex : ∀ q : Q, ∃ π : Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)),
      π ∈ Work.AUTL2.pgammaL (GaloisField p e) ∧
        ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e),
          π * Work.AUTL2.pslHom (GaloisField p e) x * π⁻¹ =
            Work.AUTL2.pslHom (GaloisField p e) (α q x) :=
    fun q => Work.AUTL2.Aut.realize p e hp hq (α q)
  let Φfun : Q → Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)) :=
    fun q => Classical.choose (hex q)
  have hΦmem : ∀ q : Q, Φfun q ∈ Work.AUTL2.pgammaL (GaloisField p e) :=
    fun q => (Classical.choose_spec (hex q)).1
  have hΦconj : ∀ (q : Q)
      (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)),
      Φfun q * Work.AUTL2.pslHom (GaloisField p e) x * (Φfun q)⁻¹ =
        Work.AUTL2.pslHom (GaloisField p e) (α q x) :=
    fun q x => (Classical.choose_spec (hex q)).2 x
  -- `Φfun` is multiplicative, by uniqueness of the realizing permutation.
  have hΦone : Φfun 1 = 1 := by
    refine realize_unique (GaloisField p e) hcent (Φfun 1) 1 (fun y => ?_)
    rw [hΦconj 1 y, map_one]
    simp
  have hΦmul : ∀ a b : Q, Φfun (a * b) = Φfun a * Φfun b := by
    intro a b
    refine realize_unique (GaloisField p e) hcent (Φfun (a * b)) (Φfun a * Φfun b) (fun y => ?_)
    rw [hΦconj (a * b) y,
      show Φfun a * Φfun b * Work.AUTL2.pslHom (GaloisField p e) y * (Φfun a * Φfun b)⁻¹
          = Φfun a * (Φfun b * Work.AUTL2.pslHom (GaloisField p e) y * (Φfun b)⁻¹)
              * (Φfun a)⁻¹ by group,
      hΦconj b y, hΦconj a (α b y),
      show α (a * b) = α a * α b from map_mul α a b]
    simp [MulAut.mul_apply]
  let Φ : Q →* Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)) :=
    { toFun := Φfun, map_one' := hΦone, map_mul' := hΦmul }
  have hΦcoe : ∀ q : Q, Φ q = Φfun q := fun q => rfl
  -- Congruence of `eiso` with the conjugation action of `Q` on `L`.
  have hconjval : ∀ (q : Q) (t : ↥L),
      ((MulAut.conjNormal (H := L) q t : ↥L) : Q) = q * (t : Q) * q⁻¹ :=
    fun q t => MulAut.conjNormal_apply q t
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · -- Clause 1: `Φ` restricts to `pslHom ∘ eiso` on `L`.
    intro x
    show Φfun (x : Q) = Work.AUTL2.pslHom (GaloisField p e) (eiso x)
    refine realize_unique (GaloisField p e) hcent (Φfun (x : Q))
      (Work.AUTL2.pslHom (GaloisField p e) (eiso x)) (fun y => ?_)
    have hval : (MulAut.conjNormal (H := L) (x : Q)) (eiso.symm y)
        = x * eiso.symm y * x⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      rfl
    rw [hΦconj (x : Q) y, hαdef (x : Q), mulAut_congr_apply, hval]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  · -- Clause 2: `Φ` lands in `PΓL(2, q)`.
    intro q
    rw [hΦcoe q]
    exact hΦmem q
  · -- Clause 3: `Φ` intertwines conjugation with the transported action.
    intro q x
    rw [hΦcoe q, hΦconj q x]
    rfl
  · -- Clause 4: the kernel of `Φ` is the centralizer of `L`.
    intro q
    constructor
    · intro hq1
      have hq1' : Φfun q = 1 := by rw [← hΦcoe q]; exact hq1
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hid : ∀ y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e),
          y = (MulAut.congr eiso) (MulAut.conjNormal (H := L) q) y := by
        intro y
        have h := hΦconj q y
        rw [hq1'] at h
        have h' : Work.AUTL2.pslHom (GaloisField p e) y =
            Work.AUTL2.pslHom (GaloisField p e) (α q y) := by simpa using h
        have h2 := hpslinj h'
        rwa [hαdef q] at h2
      have h2 : eiso ⟨t, ht⟩ = eiso ((MulAut.conjNormal (H := L) q) ⟨t, ht⟩) := by
        have h := hid (eiso ⟨t, ht⟩)
        rw [mulAut_congr_apply] at h
        simpa using h
      have h3 : (t : Q) = q * t * q⁻¹ := by
        have h4 : (⟨t, ht⟩ : ↥L) = (MulAut.conjNormal (H := L) q) ⟨t, ht⟩ := eiso.injective h2
        have h5 := congrArg (Subtype.val) h4
        rw [hconjval q ⟨t, ht⟩] at h5
        exact h5
      have h5 : q * t * q⁻¹ = t := h3.symm
      calc t * q = (q * t * q⁻¹) * q := by rw [h5]
        _ = q * t := by group
    · intro hqmem
      have hconj1 : MulAut.conjNormal (H := L) q = 1 := by
        refine MulEquiv.ext (fun t => ?_)
        show (MulAut.conjNormal (H := L) q) t = (1 : MulAut ↥L) t
        rw [MulAut.one_apply]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have ht : (t : Q) * q = q * (t : Q) :=
          (Subgroup.mem_centralizer_iff.mp hqmem) (t : Q) t.2
        rw [← ht]
        group
      have hα1 : α q = 1 := by rw [hαdef q, hconj1, map_one]
      have hmem : Φfun q ∈ Subgroup.centralizer (Work.AUTL2.pslImage (GaloisField p e) :
          Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p e)))) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro g ⟨y, rfl⟩
        have h1 : Φfun q * Work.AUTL2.pslHom (GaloisField p e) y * (Φfun q)⁻¹ =
            Work.AUTL2.pslHom (GaloisField p e) y := by
          rw [hΦconj q y, hα1]
          rfl
        calc Work.AUTL2.pslHom (GaloisField p e) y * Φfun q
            = (Φfun q * Work.AUTL2.pslHom (GaloisField p e) y * (Φfun q)⁻¹) * Φfun q := by
              rw [h1]
          _ = Φfun q * Work.AUTL2.pslHom (GaloisField p e) y := by group
      rw [hcent] at hmem
      rw [hΦcoe q]
      exact Subgroup.mem_bot.mp hmem

end Work.L2F.Props.L2Outer

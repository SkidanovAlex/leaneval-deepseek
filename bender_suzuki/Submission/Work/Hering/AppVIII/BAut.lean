/-
# Appendix VIII, Proposition 3: `Aut(B(n,1,ε))` is solvable

`B(n,1,ε)` is the Suzuki 2-group of Higman's table of type `B` with trivial `θ`, in the two-step
model `Work.Higman.BType F (RingEquiv.refl F) ε`.  Following Peterfalvi I, App. VIII, Prop. 3
(p. 226), we show:

* the centre of `B(n,1,ε)` is `kerFst = {(0,z)}` (`bType_center`);
* `K × K` with the squaring form `(a,b) ↦ a² + εab + b²` is the quadratic field extension
  `L = K[α]`, `α² = εα + 1`, and `a + bα` is additive in `(a,b)` (`quadAddEquiv`);
* if `α ∈ Aut(B(n,1,ε))` induces `f` on `B/Z ≅ K × K` and `g` on `Z ≅ K`, then `g(N x) = N(f x)`
  where `N` is the norm of `L/K`, so `f` is *semilinear*, `f x = λ · x ^ (2^i)`
  (`fstFun_semilinear`, the coefficient computation of `CoreCompute.semilinear_of_normRepr`);
* the kernel of `α ↦ f` is abelian and the semilinear maps form a solvable group, whence
  `Aut(B(n,1,ε))` is solvable (`isSolvable_mulAut_B`).
-/
import Mathlib
import Submission.Work.Higman.Family
import Submission.Work.Hering.AppVIII.QuadExt
import Submission.Work.Hering.AppVIII.QuadExtNorm
import Submission.Work.Hering.AppVIII.SemiLinAux
import Submission.Work.Hering.AppVIII.TwoStepAut
import Submission.Work.Hering.AppVIII.CoreCompute

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- `B(n,1,ε)`: Higman's family `B` with trivial `θ`, in the two-step model. -/
abbrev Bn (ε : F) : Type _ := BType F (RingEquiv.refl F) ε

/-! ## Elementary facts about `B(n,1,ε)` -/

/-- **The centre of `B(n,1,ε)`.**  For `ε ≠ 0` an element is central iff its `A`-coordinate
vanishes. -/
theorem bType_center {ε : F} (hε : ε ≠ 0) (x : Bn ε) :
    x ∈ Subgroup.center (Bn ε) ↔ x.fst = 0 := by
  refine ⟨fun h => ?_, fun h => TwoStep.kerFst_le_center h⟩
  rw [TwoStep.mem_center_iff] at h
  have h1 := h (0, 1)
  have h2 := h (1, 0)
  have ha : x.fst.1 = 0 := by
    have key : ε * x.fst.1 = 0 := by
      have h1' : ε * x.fst.1 + x.fst.2 = x.fst.2 := by simpa [bCocycle] using h1
      exact add_right_cancel (by rw [h1', zero_add])
    exact (mul_eq_zero.mp key).resolve_left hε
  have hc : x.fst.2 = 0 := by
    have key : ε * x.fst.2 = 0 := by
      have h2' : x.fst.1 = x.fst.1 + ε * x.fst.2 := by simpa [bCocycle] using h2
      exact add_left_cancel (by rw [h2'.symm, add_zero])
    exact (mul_eq_zero.mp key).resolve_left hε
  exact Prod.ext ha hc

/-- **The squaring map of `B(n,1,ε)` is onto** (`u = (√z, 0)` works). -/
theorem bType_sq_surj (ε : F) (z : F) :
    ∃ u : F × F, bCocycle F (RingEquiv.refl F) ε u u = z := by
  refine ⟨(sqrtF F z, 0), ?_⟩
  rw [show bCocycle F (RingEquiv.refl F) ε (sqrtF F z, 0) (sqrtF F z, 0)
      = sqrtF F z * sqrtF F z by simp [bCocycle], ← pow_two]
  exact sqrtF_sq F z

/-- **`K × K` is `K[α]` additively**: `(a,b) ↦ a + bα` is an additive equivalence. -/
theorem quadAddEquiv {ε : F} [Fact (Irreducible (quadPoly F ε))] :
    ∃ e : (F × F) ≃+ QuadExt F ε, ∀ p : F × F,
      e p = algebraMap F (QuadExt F ε) p.1 + algebraMap F (QuadExt F ε) p.2 * qalpha F ε := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (QuadExt F ε) := Fintype.ofFinite _
  let f : (F × F) →+ QuadExt F ε :=
    { toFun := fun p =>
        algebraMap F (QuadExt F ε) p.1 + algebraMap F (QuadExt F ε) p.2 * qalpha F ε
      map_zero' := by simp
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨p, hp⟩ := exists_repr F ε x
    exact ⟨p, by
      show f p = x
      rw [show f p = algebraMap F (QuadExt F ε) p.1
        + algebraMap F (QuadExt F ε) p.2 * qalpha F ε from rfl, hp]⟩
  have hcard : Fintype.card (F × F) = Fintype.card (QuadExt F ε) := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← pow_two]
    exact (quadExt_natCard F ε).symm
  have hinj : Function.Injective f :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mpr hsurj
  exact ⟨AddEquiv.ofBijective f ⟨hinj, hsurj⟩, fun p => rfl⟩

/-! ## The semilinear group of `L = K[α]`, transported to `K × K` -/

/-- Conjugation of permutations by an equivalence. -/
def permConj {α β : Type*} (e : α ≃ β) : Equiv.Perm α →* Equiv.Perm β where
  toFun := e.permCongr
  map_one' := e.permCongr_refl
  map_mul' p q := by
    rw [Equiv.Perm.mul_def, Equiv.Perm.mul_def, ← Equiv.permCongr_trans e q p]

theorem permConj_injective {α β : Type*} (e : α ≃ β) :
    Function.Injective (permConj e) := fun p q h => e.permCongr.injective h

/-- The "semilinear" subgroup of `Equiv.Perm (K × K)`, transported from the group
`{x ↦ λ · x ^ (2^i)}` of semilinear maps of `L = K[α]`. -/
def semiB {ε : F} [Fact (Irreducible (quadPoly F ε))] (e : (F × F) ≃+ QuadExt F ε) :
    Subgroup (Equiv.Perm (F × F)) :=
  (gammaLin (QuadExt F ε)).comap (permConj e.toEquiv)

theorem semiB_solvable {ε : F} [Fact (Irreducible (quadPoly F ε))]
    (e : (F × F) ≃+ QuadExt F ε) : Group.IsSolvable (semiB e) := by
  haveI : Group.IsSolvable (gammaLin (QuadExt F ε)) := inferInstance
  let ρ : semiB e →* gammaLin (QuadExt F ε) :=
    ((permConj e.toEquiv).comp (semiB e).subtype).codRestrict _
      (fun x => (Subgroup.mem_comap).mp x.2)
  have hρ : Function.Injective ρ := by
    intro x y h
    refine Subtype.ext ?_
    exact permConj_injective e.toEquiv (congrArg Subtype.val h)
  exact Group.isSolvable_of_isSolvable_injective hρ

/-- `(frobK L ^ i) x = x ^ (2^i)` for `i : ℕ` (as a power of the Frobenius). -/
theorem frobK_zpow_natCast_apply {ε : F} [Fact (Irreducible (quadPoly F ε))] (i : ℕ)
    (x : QuadExt F ε) : (frobK (QuadExt F ε) ^ (i : ℤ)) x = x ^ (2 ^ i) := by
  have h : frobK (QuadExt F ε) = frobeniusEquiv (QuadExt F ε) 2 := rfl
  rw [zpow_natCast, h, ← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def]

/-- **The coefficient computation of App. VIII Prop. 3.**  If `α ∈ Aut(B(n,1,ε))` induces `f` on
`B/Z ≅ K × K` (where `e : K × K ≃ K[α]` identifies the two), then `f` is semilinear:
`e (f u) = λ · (e u) ^ (2^i)`. -/
theorem fstFun_semilinear {ε : F} [Fact (Irreducible (quadPoly F ε))] (hε : Anisotropic F ε)
    (e : (F × F) ≃+ QuadExt F ε)
    (he : ∀ p : F × F, e p = algebraMap F (QuadExt F ε) p.1
      + algebraMap F (QuadExt F ε) p.2 * qalpha F ε)
    (α : MulAut (Bn ε)) :
    ∃ (a : QuadExt F ε) (i : ℕ), a ≠ 0 ∧
      ∀ u : F × F, e (TSA.fstFun α u) = a * (e u) ^ (2 ^ i) := by
  classical
  have hε0 : ε ≠ 0 := eps_ne_zero F hε
  have hZ : ∀ x : Bn ε, x ∈ Subgroup.center (Bn ε) ↔ x.fst = 0 := bType_center hε0
  have hq : ∀ z : F, ∃ u : F × F, bCocycle F (RingEquiv.refl F) ε u u = z :=
    bType_sq_surj ε
  -- the induced additive maps
  let fα : (F × F) →+ (F × F) := AddMonoidHom.mk' (TSA.fstFun α) (TSA.fstFun_add hZ α)
  have hfα : Function.Bijective fα := TSA.fstFun_bijective hZ α
  let fαe : (F × F) ≃+ (F × F) := AddEquiv.ofBijective fα hfα
  let gα : F →+ F := AddMonoidHom.mk' (TSA.sndFun α) (TSA.sndFun_add hZ α)
  let gαe : F ≃+ F := AddEquiv.ofBijective gα (TSA.sndFun_bijective hZ α)
  let Fα : QuadExt F ε ≃+ QuadExt F ε := e.symm.trans (fαe.trans e)
  have hFα_apply : ∀ x : QuadExt F ε, Fα x = e (fα (e.symm x)) := fun x => rfl
  -- the two-step squaring relation in coordinates
  have hquad : ∀ a b : F,
      TSA.sndFun α (a * a + ε * (a * b) + b * b)
        = (TSA.fstFun α (a, b)).1 * (TSA.fstFun α (a, b)).1
          + ε * ((TSA.fstFun α (a, b)).1 * (TSA.fstFun α (a, b)).2)
          + (TSA.fstFun α (a, b)).2 * (TSA.fstFun α (a, b)).2 := fun a b => by
    have h := TSA.sndFun_quad (b := bCocycle F (RingEquiv.refl F) ε) α (a, b)
    rwa [show bCocycle F (RingEquiv.refl F) ε (a, b) (a, b)
        = a * a + ε * (a * b) + b * b from by simp [bCocycle],
      show bCocycle F (RingEquiv.refl F) ε (TSA.fstFun α (a, b)) (TSA.fstFun α (a, b))
        = (TSA.fstFun α (a, b)).1 * (TSA.fstFun α (a, b)).1
          + ε * ((TSA.fstFun α (a, b)).1 * (TSA.fstFun α (a, b)).2)
          + (TSA.fstFun α (a, b)).2 * (TSA.fstFun α (a, b)).2 from by simp [bCocycle]] at h
  -- the norm relation
  have hnorm : ∀ a b : F,
      algebraMap F (QuadExt F ε) (gαe (a * a + ε * (a * b) + b * b))
        = Fα (algebraMap F (QuadExt F ε) a + algebraMap F (QuadExt F ε) b * qalpha F ε)
          * (Fα (algebraMap F (QuadExt F ε) a + algebraMap F (QuadExt F ε) b
              * qalpha F ε)) ^ (Nat.card F) := by
    intro a b
    have hFeq : Fα (algebraMap F (QuadExt F ε) a + algebraMap F (QuadExt F ε) b * qalpha F ε)
        = e (TSA.fstFun α (a, b)) := by
      rw [← he (a, b)]
      rw [hFα_apply, AddEquiv.symm_apply_apply]
      rfl
    have hstep : e (TSA.fstFun α (a, b)) * (e (TSA.fstFun α (a, b))) ^ (Nat.card F)
        = algebraMap F (QuadExt F ε) (TSA.sndFun α (a * a + ε * (a * b) + b * b)) := by
      rw [hquad a b, he (TSA.fstFun α (a, b)),
        normRepr F hε (TSA.fstFun α (a, b)).1 (TSA.fstFun α (a, b)).2]
    rw [hFeq, hstep]
    rfl
  obtain ⟨lam, i, hlam, hF⟩ :=
    semilinear_of_normRepr (K := F) (ε := ε) hε Fα gαe hnorm
  refine ⟨lam, i, hlam, fun u => ?_⟩
  have h2 : Fα (e u) = e (TSA.fstFun α u) := by
    rw [hFα_apply, AddEquiv.symm_apply_apply]
    rfl
  rw [← h2]
  exact hF (e u)

/-! ## Assembly: `Aut(B(n,1,ε))` is solvable -/

/-- **App. VIII, Prop. 3.**  If `ε` satisfies the anisotropy condition of the source, then
`Aut(B(n,1,ε))` is solvable. -/
theorem isSolvable_mulAut_B {ε : F} (hε : Anisotropic F ε) :
    Group.IsSolvable (MulAut (Bn ε)) := by
  classical
  haveI : Fact (Irreducible (quadPoly F ε)) := ⟨quadPoly_irreducible F hε⟩
  have hε0 : ε ≠ 0 := eps_ne_zero F hε
  have hZ : ∀ x : Bn ε, x ∈ Subgroup.center (Bn ε) ↔ x.fst = 0 := bType_center hε0
  have hq : ∀ z : F, ∃ u : F × F, bCocycle F (RingEquiv.refl F) ε u u = z :=
    bType_sq_surj ε
  obtain ⟨e, he⟩ := quadAddEquiv (F := F) (ε := ε)
  let S : Subgroup (Equiv.Perm (F × F)) := semiB e
  haveI hSsolv : Group.IsSolvable S := semiB_solvable e
  -- the homomorphism `α ↦ fstFun α`
  have hbi : ∀ α : MulAut (Bn ε), Function.Bijective (TSA.fstFun α) := fun α =>
    TSA.fstFun_bijective hZ α
  let Φfun : MulAut (Bn ε) → Equiv.Perm (F × F) := fun α =>
    Equiv.ofBijective (TSA.fstFun α) (hbi α)
  have hΦmul : ∀ α β : MulAut (Bn ε), Φfun (α * β) = Φfun α * Φfun β := by
    intro α β
    apply Equiv.ext
    intro u
    show Φfun (α * β) u = Φfun α (Φfun β u)
    simp only [Φfun, Equiv.ofBijective_apply]
    rw [TSA.fstFun_mul hZ]
    rfl
  have hΦone : Φfun 1 = 1 := by
    apply Equiv.ext
    intro u
    show Φfun 1 u = (1 : Equiv.Perm (F × F)) u
    simp only [Φfun, Equiv.ofBijective_apply, TSA.fstFun_one]
    rfl
  let Φ : MulAut (Bn ε) →* Equiv.Perm (F × F) :=
    { toFun := Φfun, map_one' := hΦone, map_mul' := hΦmul }
  have hfstN : ∀ a : Φ.ker, TSA.fstFun ((a : MulAut (Bn ε))) = id := by
    intro a
    have hmem : Φ (a : MulAut (Bn ε)) = 1 := MonoidHom.mem_ker.mp a.2
    funext u
    have h := congrArg (fun e : Equiv.Perm (F × F) => e u) hmem
    simpa [Φ, Φfun, Equiv.ofBijective_apply] using h
  have hNcomm : ∀ a b : Φ.ker, a * b = b * a := by
    intro a b
    refine Subtype.ext ?_
    exact TSA.kernel_comm hZ hq (a : MulAut (Bn ε)) (b : MulAut (Bn ε)) (hfstN a) (hfstN b)
  have hNsolv : Group.IsSolvable Φ.ker := Group.isSolvable_of_comm hNcomm
  -- the image lies in the semilinear subgroup
  have hmemS : ∀ α : MulAut (Bn ε), Φfun α ∈ S := by
    intro α
    obtain ⟨a, i, ha, hconcl⟩ := fstFun_semilinear hε e he α
    change permConj e.toEquiv (Φfun α) ∈ gammaLin (QuadExt F ε)
    refine ⟨a, (i : ℤ), ha, ?_⟩
    intro x
    have hx : e (TSA.fstFun α (e.symm x)) = a * x ^ (2 ^ i) := by
      have h := hconcl (e.symm x)
      rwa [AddEquiv.apply_symm_apply] at h
    have hcalcx : permConj e.toEquiv (Φfun α) x
        = e (TSA.fstFun α (e.symm x)) := by
      show e.toEquiv.permCongr (Φfun α) x = e (TSA.fstFun α (e.symm x))
      rw [Equiv.permCongr_apply]
      rfl
    rw [hcalcx, hx, frobK_zpow_natCast_apply]
  have hcod : ∀ y : (MulAut (Bn ε)) ⧸ Φ.ker, QuotientGroup.kerLift Φ y ∈ S := by
    intro y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective Φ.ker y
    simpa [Φ, QuotientGroup.kerLift_mk] using hmemS α
  let Ψ : (MulAut (Bn ε)) ⧸ Φ.ker →* S :=
    MonoidHom.codRestrict (QuotientGroup.kerLift Φ) S hcod
  have hQ : Group.IsSolvable ((MulAut (Bn ε)) ⧸ Φ.ker) := by
    have hinj : Function.Injective Ψ := by
      intro y y' h
      exact QuotientGroup.kerLift_injective Φ (congrArg Subtype.val h)
    exact Group.isSolvable_of_isSolvable_injective hinj
  haveI := hNsolv
  haveI := hQ
  exact Group.isSolvable_of_subgroup_quotient Φ.ker

end Work.Hering.AppVIII

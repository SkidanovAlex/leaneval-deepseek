import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.GL32.AppIXNatIrreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: the permutation module `k[Ω]` on the `21` pairs of points of `PG(2,2)`

`Ω` is the set of unordered pairs of distinct nonzero vectors of `V = F₂³`.  `GL(3,2)` acts on
`V`, hence on `Ω`, hence on `W = k[Ω]` (`k = F₂`), the **permutation module of dimension `21`**.

We construct four natural `GL(3,2)`-equivariant linear maps out of `W`:

* `aug : W → k` (`f ↦ Σ f`),
* `phi : W → V` (`f ↦ Σ f(p) • (a+b)` for `p = {a,b}`),
* `psi : W → V*` (`f ↦ Σ f(p) • (x ↦ det(a,b,x))`),
* `theta : W → M₄` (`f ↦ Σ f(p) • (x ↦ det(a,b,x) • (a+b))`, a trace-zero endomorphism),

together with the transposed maps `phiStar : V* → W`, `psiStar : V → W`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Hering.GL32

/-- The nonzero vectors of `F₂³`, i.e. the points of `PG(2,2)`. -/
abbrev Pt : Type := {v : F2v // v ≠ 0}

/-- The set `Ω` of unordered pairs of distinct points. -/
abbrev Pair : Type := {s : Sym2 Pt // ¬ s.IsDiag}

instance instFintypePt : Fintype Pt := inferInstance
instance instDecidableEqPt : DecidableEq Pt := inferInstance
instance instFintypePair : Fintype Pair := inferInstance
instance instDecidableEqPair : DecidableEq Pair := inferInstance

/-- The permutation of `Pt` induced by `g : GL32`. -/
def ptPerm (g : GL32) : Pt ≃ Pt where
  toFun v := ⟨g v.1, fun h => v.2 (g.injective (by simpa using h))⟩
  invFun v := ⟨g.symm v.1, fun h => v.2 (g.symm.injective (by simpa using h))⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

lemma ptPerm_coe (g : GL32) (v : Pt) : (ptPerm g v : F2v) = g v.1 := rfl
lemma ptPerm_symm_coe (g : GL32) (v : Pt) : (ptPerm g.symm v : F2v) = g.symm v.1 := rfl

/-- The permutation of `Ω` induced by `g : GL32`. -/
def pairPerm (g : GL32) : Pair ≃ Pair where
  toFun p := ⟨Sym2.map (ptPerm g) p.1, by
    rw [Sym2.isDiag_map (ptPerm g).injective]; exact p.2⟩
  invFun p := ⟨Sym2.map (ptPerm g.symm) p.1, by
    rw [Sym2.isDiag_map (ptPerm g.symm).injective]; exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    show Sym2.map (ptPerm g.symm) (Sym2.map (ptPerm g) p.1) = p.1
    have h : (ptPerm g.symm : Pt → Pt) ∘ (ptPerm g : Pt → Pt) = id := by
      funext v; exact Equiv.left_inv (ptPerm g) v
    calc Sym2.map (ptPerm g.symm) (Sym2.map (ptPerm g) p.1)
        = (Sym2.map (ptPerm g.symm) ∘ Sym2.map (ptPerm g)) p.1 := rfl
      _ = Sym2.map ((ptPerm g.symm : Pt → Pt) ∘ (ptPerm g : Pt → Pt)) p.1 := by
            rw [Sym2.map_comp]
      _ = Sym2.map (id : Pt → Pt) p.1 := by rw [h]
      _ = p.1 := by rw [Sym2.map_id]; rfl
  right_inv p := by
    apply Subtype.ext
    show Sym2.map (ptPerm g) (Sym2.map (ptPerm g.symm) p.1) = p.1
    have h : (ptPerm g : Pt → Pt) ∘ (ptPerm g.symm : Pt → Pt) = id := by
      funext v; exact Equiv.right_inv (ptPerm g) v
    calc Sym2.map (ptPerm g) (Sym2.map (ptPerm g.symm) p.1)
        = (Sym2.map (ptPerm g) ∘ Sym2.map (ptPerm g.symm)) p.1 := rfl
      _ = Sym2.map ((ptPerm g : Pt → Pt) ∘ (ptPerm g.symm : Pt → Pt)) p.1 := by
            rw [Sym2.map_comp]
      _ = Sym2.map (id : Pt → Pt) p.1 := by rw [h]
      _ = p.1 := by rw [Sym2.map_id]; rfl

/-- The permutation module `W = k[Ω]`. -/
abbrev W : Type := Pair → ZMod 2

/-- The action of `GL(3,2)` on `W`. -/
noncomputable def actW (g : GL32) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (pairPerm g).symm

lemma actW_apply (g : GL32) (f : W) :
    actW g f = f ∘ (⇑(pairPerm g).symm : Pair → Pair) := rfl

/-- The sum of the two points of a pair. -/
noncomputable def psum : Pair → F2v :=
  fun p => Sym2.lift ⟨fun a b : Pt => a.1 + b.1, fun a b => add_comm _ _⟩ p.1

/-- The determinant of three vectors of `F₂³` (the columns of the matrix `[x y z]`). -/
def det3 (x y z : F2v) : ZMod 2 := (Matrix.of ![x, y, z]).transpose.det

/-- In `F₂`, `-t = t`. -/
lemma neg_eq_self_zmod2 (t : ZMod 2) : -t = t := by revert t; decide

lemma det3_swap (x y z : F2v) : det3 y x z = det3 x y z := by
  have h : det3 y x z + det3 x y z = 0 := by
    rw [det3, det3, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    ring
  have h2 : det3 x y z = -det3 y x z := eq_neg_of_add_eq_zero_right h
  rw [CharTwo.neg_eq] at h2
  exact h2.symm

/-- The determinant of the matrix of a linear equivalence is `1` (the only unit of `F₂`). -/
lemma toMatrix'_det_eq_one (g : GL32) :
    (LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)).det = 1 := by
  have hmul : LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v) *
      LinearMap.toMatrix' ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v) = 1 := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    ext v
    simp
  have hdet : (LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)).det *
      (LinearMap.toMatrix' ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v)).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hne : (LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)).det ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by intro x; revert x; decide)
    ((LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)).det) with h | h
  · exact absurd h hne
  · exact h

/-- **Invariance of `det3`** under `GL(3,2)` (which has determinant one). -/
lemma det3_mul (g : GL32) (x y z : F2v) : det3 (g x) (g y) (g z) = det3 x y z := by
  have key : (Matrix.of ![g x, g y, g z]).transpose =
      LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v) * (Matrix.of ![x, y, z]).transpose := by
    ext k l
    have hL : (Matrix.of ![g x, g y, g z]).transpose k l = (g (![x, y, z] l)) k := by
      fin_cases l <;> simp [Matrix.transpose_apply]
    have hM : (g (![x, y, z] l)) k =
        ((LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)).mulVec (![x, y, z] l)) k := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [hL, Matrix.mul_apply, hM]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun m _ => by simp [Matrix.transpose_apply])
  rw [det3, det3, key, Matrix.det_mul, toMatrix'_det_eq_one g, one_mul]

lemma pairPerm_symm_eq (g : GL32) (q : Pair) :
    (pairPerm g).symm q = pairPerm (g.symm) q := rfl

lemma actW_single (g : GL32) (p : Pair) :
    actW g (Pi.single p (1 : ZMod 2)) = Pi.single (pairPerm g p) 1 := by
  ext q
  rw [actW_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : q = pairPerm g p
  · rw [if_pos ((Equiv.symm_apply_eq (pairPerm g)).mpr h), if_pos h]
  · rw [if_neg (fun hh => h ((Equiv.symm_apply_eq (pairPerm g)).mp hh)), if_neg h]

lemma psum_pairPerm (g : GL32) (p : Pair) : psum (pairPerm g p) = g (psum p) := by
  obtain ⟨s, hs⟩ := p
  induction s using Sym2.ind with
  | h a b =>
      have h1 : (pairPerm g ⟨Sym2.mk a b, hs⟩).1 = Sym2.mk (ptPerm g a) (ptPerm g b) := by
        show Sym2.map (ptPerm g) (Sym2.mk a b) = _
        rw [Sym2.map_mk]
      show psum (pairPerm g ⟨Sym2.mk a b, hs⟩) = g (psum ⟨Sym2.mk a b, hs⟩)
      simp only [psum, h1, Sym2.lift_mk]
      rw [ptPerm_coe, ptPerm_coe, map_add]

/-! ## The linear functionals attached to a pair -/

/-- The linear functional `x ↦ det3 a b x` attached to an ordered pair of points. -/
noncomputable def det3Lin (a b : Pt) : Module.Dual (ZMod 2) F2v where
  toFun x := det3 a.1 b.1 x
  map_add' x y := by
    simp only [det3, Matrix.det_fin_three, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Pi.add_apply]
    ring
  map_smul' c x := by
    simp only [det3, Matrix.det_fin_three, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma det3Lin_swap (a b : Pt) : det3Lin a b = det3Lin b a := by
  apply LinearMap.ext
  intro x
  show det3 a.1 b.1 x = det3 b.1 a.1 x
  exact det3_swap b.1 a.1 x

/-- The "wedge" functional of a pair: `x ↦ det(a,b,x)`. -/
noncomputable def pdF : Pair → Module.Dual (ZMod 2) F2v :=
  fun p => Sym2.lift ⟨fun a b : Pt => det3Lin a b, fun a b => det3Lin_swap a b⟩ p.1

lemma pdF_pairPerm (g : GL32) (p : Pair) :
    pdF (pairPerm g p) = (g.symm : GL32).dualMap (pdF p) := by
  obtain ⟨s, hs⟩ := p
  induction s using Sym2.ind with
  | h a b =>
      have h1 : (pairPerm g ⟨Sym2.mk a b, hs⟩).1 = Sym2.mk (ptPerm g a) (ptPerm g b) := by
        show Sym2.map (ptPerm g) (Sym2.mk a b) = _
        rw [Sym2.map_mk]
      show pdF (pairPerm g ⟨Sym2.mk a b, hs⟩) = _
      simp only [pdF, h1, Sym2.lift_mk]
      apply LinearMap.ext
      intro x
      rw [LinearEquiv.dualMap_apply]
      show det3 (g a.1) (g b.1) x = det3 a.1 b.1 (g.symm x)
      have h3 : det3 (g a.1) (g b.1) x = det3 (g a.1) (g b.1) (g (g.symm x)) := by
        rw [LinearEquiv.apply_symm_apply]
      rw [h3, det3_mul]

/-! ## The four maps out of `W` -/

/-- The augmentation `W → k`. -/
noncomputable def aug : W →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ p : Pair, f p
  map_add' f h := by simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by simp [Pi.smul_apply, Finset.mul_sum]

/-- The natural map `W → V`, `f ↦ Σ f(p) • (a+b)`. -/
noncomputable def phi : W →ₗ[ZMod 2] F2v where
  toFun f := ∑ p : Pair, f p • psum p
  map_add' f h := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

/-- The map `W → V*`, `f ↦ Σ f(p) • (x ↦ det(a,b,x))`. -/
noncomputable def psi : W →ₗ[ZMod 2] Module.Dual (ZMod 2) F2v where
  toFun f := ∑ p : Pair, f p • pdF p
  map_add' f h := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

lemma aug_single (p : Pair) : aug (Pi.single p (1 : ZMod 2)) = 1 := by
  simp [aug]

lemma phi_single (p : Pair) : phi (Pi.single p (1 : ZMod 2)) = psum p := by
  simp [phi]

lemma psi_single (p : Pair) : psi (Pi.single p (1 : ZMod 2)) = pdF p := by
  simp [psi]

/-- The basis expansion in `W`. -/
lemma eq_sum_smul_single (f : W) : f = ∑ p : Pair, f p • (Pi.single p (1 : ZMod 2) : W) := by
  rw [← Finset.univ_sum_single f]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  funext q
  simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : q = p
  · subst h; simp
  · simp [h]

lemma aug_actW (g : GL32) (f : W) : aug (actW g f) = aug f := by
  conv_lhs => rw [eq_sum_smul_single f]
  conv_rhs => rw [eq_sum_smul_single f]
  simp only [map_sum, map_smul, actW_single, aug_single, smul_eq_mul, mul_one]

lemma phi_actW (g : GL32) (f : W) : phi (actW g f) = g (phi f) := by
  conv_lhs => rw [eq_sum_smul_single f]
  conv_rhs => rw [eq_sum_smul_single f]
  simp only [map_sum, map_smul, actW_single, phi_single, psum_pairPerm]

lemma psi_actW (g : GL32) (f : W) :
    psi (actW g f) = (g.symm : GL32).dualMap (psi f) := by
  conv_lhs => rw [eq_sum_smul_single f]
  conv_rhs => rw [eq_sum_smul_single f]
  simp only [map_sum, map_smul, actW_single, psi_single, pdF_pairPerm]

/-! ## The transposed maps -/

/-- The transpose `V* → W` of `phi`: `s ↦ Σ s(psum p) • δ_p`. -/
noncomputable def phiStar : Module.Dual (ZMod 2) F2v →ₗ[ZMod 2] W where
  toFun s := ∑ p : Pair, s (psum p) • (Pi.single p (1 : ZMod 2) : W)
  map_add' s t := by
    simp only [LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c s := by
    show (∑ p : Pair, (c • s) (psum p) • (Pi.single p (1 : ZMod 2) : W)) =
      c • (∑ p : Pair, s (psum p) • (Pi.single p (1 : ZMod 2) : W))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [LinearMap.smul_apply, smul_assoc]

/-- The transpose `V → W` of `psi`: `v ↦ Σ det(a,b,v) • δ_p`. -/
noncomputable def psiStar : F2v →ₗ[ZMod 2] W where
  toFun v := ∑ p : Pair, (pdF p) v • (Pi.single p (1 : ZMod 2) : W)
  map_add' s t := by
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c s := by
    show (∑ p : Pair, (pdF p) (c • s) • (Pi.single p (1 : ZMod 2) : W)) =
      c • (∑ p : Pair, (pdF p) s • (Pi.single p (1 : ZMod 2) : W))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [map_smul, smul_assoc]

lemma phiStar_apply (s : Module.Dual (ZMod 2) F2v) (q : Pair) :
    phiStar s q = s (psum q) := by
  have h : phiStar s = ∑ p : Pair, s (psum p) • (Pi.single p (1 : ZMod 2) : W) := rfl
  rw [h, Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma psiStar_apply (v : F2v) (q : Pair) : psiStar v q = (pdF q) v := by
  have h : psiStar v = ∑ p : Pair, (pdF p) v • (Pi.single p (1 : ZMod 2) : W) := rfl
  rw [h, Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma psiStar_actV (g : GL32) (v : F2v) : psiStar (g v) = actW g (psiStar v) := by
  ext q
  rw [actW_apply, Function.comp_apply, psiStar_apply, psiStar_apply]
  rw [pairPerm_symm_eq, pdF_pairPerm (g.symm : GL32) q, LinearEquiv.dualMap_apply]
  rw [LinearEquiv.symm_symm]

lemma phiStar_actVstar (g : GL32) (s : Module.Dual (ZMod 2) F2v) :
    phiStar ((g.symm : GL32).dualMap s) = actW g (phiStar s) := by
  ext q
  rw [actW_apply, Function.comp_apply, phiStar_apply, phiStar_apply]
  rw [LinearEquiv.dualMap_apply, pairPerm_symm_eq, ← psum_pairPerm (g.symm : GL32) q]

end Work.Hering.GL32

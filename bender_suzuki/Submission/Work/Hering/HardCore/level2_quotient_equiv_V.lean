import Mathlib
import Submission.Work.Hering.HardCore.abelian_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The image of the second level in `G/V` is isomorphic to `V` via squaring

In the abelian configuration of the hard core of Hering's theorem, let `V ⊴ G` be elementary
abelian, `C = C_G(V)` be abelian with `Ω₁(C) = V` (`hinv`), and suppose that squaring maps the
second level `level2 V C = {x ∈ C | x * x ∈ V}` onto `V` (`hsq`).  Then the squaring map induces
an isomorphism

`level2 · V / V ≃* V`,  `x·V ↦ x * x`.

The two ingredients are:

* the squaring map `sq : level2 → V`, `x ↦ x * x`, is a homomorphism (`C` is abelian) which is
  onto `V` by `hsq`, and whose kernel consists of the `x` with `x * x = 1`, i.e. of the elements
  of `V` (`hinv` + `mem_V_iff`);
* the natural map `level2 → (level2 · V)/V`, `x ↦ xV`, is onto with the same kernel, so that
  `level2/V ≃ (level2 · V)/V` by the first isomorphism theorem.
-/

namespace Work.Hering.HardCore

theorem level2_quotient_equiv_V {G : Type*} [Group G] [Finite G] (V C : Subgroup G) [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hexp : ∀ x ∈ V, x * x = 1)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hsq : ∀ v ∈ V, ∃ x ∈ level2 V C hC hCab hexp, x * x = v) :
    ∃ e : ↥((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)) ≃* ↥V,
      ∀ y (hy : y ∈ level2 V C hC hCab hexp),
        e ⟨QuotientGroup.mk' V y, Subgroup.mem_map_of_mem (QuotientGroup.mk' V) hy⟩
          = ⟨y * y, hy.2⟩ := by
  classical
  let L : Subgroup G := level2 V C hC hCab hexp
  -- the squaring map on the second level, with values in `V`
  let sq : ↥L →* ↥V :=
    { toFun := fun x => ⟨(x : G) * (x : G), x.2.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hcomm : (x : G) * (y : G) = (y : G) * (x : G) := hCab _ x.2.1 _ y.2.1
        show ((x : G) * (y : G)) * ((x : G) * (y : G))
          = ((x : G) * (x : G)) * ((y : G) * (y : G))
        calc ((x : G) * (y : G)) * ((x : G) * (y : G))
            = (x : G) * ((y : G) * (x : G)) * (y : G) := by group
          _ = (x : G) * ((x : G) * (y : G)) * (y : G) := by rw [hcomm]
          _ = ((x : G) * (x : G)) * ((y : G) * (y : G)) := by group }
  -- the natural map from the second level to its image in `G/V`
  let F : ↥L →* ↥(L.map (QuotientGroup.mk' V)) :=
    { toFun := fun x => ⟨QuotientGroup.mk' V (x : G), Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  have hsq_surj : Function.Surjective sq := by
    intro v
    obtain ⟨x, hxL, hxv⟩ := hsq v v.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hxv⟩
  have hF_surj : Function.Surjective F := by
    intro z
    obtain ⟨x, hxL, hxz⟩ := Subgroup.mem_map.mp z.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hxz⟩
  -- both maps have the same kernel, namely `V ∩ C₂ = V`
  have hker : F.ker = sq.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : ((x : G) : G ⧸ V) = 1 := by
        have := congrArg (fun t : ↥(L.map (QuotientGroup.mk' V)) => (t : G ⧸ V)) h
        simpa [F] using this
      rw [QuotientGroup.eq_one_iff] at h1
      exact Subtype.ext ((mem_V_iff V C hexp hinv x.2.1).mp h1)
    · intro h
      have h2 : (x : G) * (x : G) = 1 := by
        have := congrArg (fun t : ↥V => (t : G)) h
        simpa [sq] using this
      have h1 : (x : G) ∈ V := (mem_V_iff V C hexp hinv x.2.1).mpr h2
      apply Subtype.ext
      show QuotientGroup.mk' V (x : G) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h1
  -- the two first isomorphism theorems, glued along the equality of the kernels
  let A : ↥L ⧸ F.ker ≃* ↥(L.map (QuotientGroup.mk' V)) :=
    QuotientGroup.quotientKerEquivOfSurjective F hF_surj
  let B : ↥L ⧸ F.ker ≃* ↥L ⧸ sq.ker := QuotientGroup.quotientMulEquivOfEq hker
  let D : ↥L ⧸ sq.ker ≃* ↥V := QuotientGroup.quotientKerEquivOfSurjective sq hsq_surj
  let e : ↥(L.map (QuotientGroup.mk' V)) ≃* ↥V := A.symm.trans (B.trans D)
  have htrans : ∀ z, e z = D (B (A.symm z)) := fun z => rfl
  have hD : ∀ x : ↥L, D (QuotientGroup.mk x) = sq x := fun x => rfl
  have hB : ∀ x : ↥L, B (QuotientGroup.mk x) = QuotientGroup.mk x := fun x => rfl
  have hA : ∀ x : ↥L, A (QuotientGroup.mk x)
      = (⟨QuotientGroup.mk' V (x : G),
          Subgroup.mem_map_of_mem _ x.2⟩ : ↥(L.map (QuotientGroup.mk' V))) := fun x => rfl
  refine ⟨e, ?_⟩
  intro y hy
  have hL : y ∈ L := hy
  have hmem : QuotientGroup.mk' V y ∈ L.map (QuotientGroup.mk' V) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' V) hL
  have hsymm : A.symm (⟨QuotientGroup.mk' V y, hmem⟩ : ↥(L.map (QuotientGroup.mk' V)))
      = QuotientGroup.mk (⟨y, hL⟩ : ↥L) := by
    rw [← hA ⟨y, hL⟩, MulEquiv.symm_apply_apply]
  have key : e (⟨QuotientGroup.mk' V y, hmem⟩ : ↥(L.map (QuotientGroup.mk' V))) = sq ⟨y, hL⟩ := by
    rw [htrans, hsymm, hB, hD]
  exact key

end Work.Hering.HardCore

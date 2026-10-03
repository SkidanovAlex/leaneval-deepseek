import Mathlib
import Submission.Work.ORBridgeLinnell.Basic

namespace Work.ORBridgeLinnell

open Work.ORVonNeumann

/-! ## Conjugation of the division closure `D H`

The division closure `D H = D_{K[H]}(U(G))` of `K[H]` inside `U(G)` is not merely a subring of
`U(G)`: it is the formal-consequence part of the Linnell datum **(I2)**, which says that
`D H` is carried to `D H^g` by conjugation with the group basis element `g ∈ G`.  Since `D H`
is defined as a *division closure* (a minimal division closed subring containing the image of
`K[H] → U(G)`), this is a formal consequence of minimality: conjugation by the unit `gen g` is a
`K`-linear ring automorphism of `U(G)` sending the image of `K[H]` to the image of `K[H^g]`, and
it preserves division closedness.

We organise this by showing that the subring
`C := {y : U(G) | gen g * y * (gen g)⁻¹ ∈ D (H^g)}`
is division closed and contains the image of `K[H]`; the minimality `D_minimal` then gives
`D H ≤ C`, which is the desired statement.

The only technical input is that `y ↦ c * y * ci` for a unit `c` (with `ci = c⁻¹`) is a ring
homomorphism of `U(G)` which is `K`-linear — because the image of `algebraMap K U(G)` is
central. -/

/-- Conjugation `y ↦ c * y * ci` by a pair of mutually inverse elements of a ring is a ring
homomorphism. -/
noncomputable def conjRingHom {S : Type*} [Ring S] (c ci : S) (hc : c * ci = 1)
    (hc' : ci * c = 1) : S →+* S where
  toFun y := c * y * ci
  map_one' := by rw [mul_one, hc]
  map_mul' y z := by
    simp only [mul_assoc]
    rw [← mul_assoc ci c (z * ci), hc', one_mul]
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' y z := by rw [mul_add, add_mul]

@[simp]
theorem conjRingHom_apply {S : Type*} [Ring S] (c ci : S) (hc : c * ci = 1) (hc' : ci * c = 1)
    (y : S) : conjRingHom c ci hc hc' y = c * y * ci := rfl

/-- `conjRingHom` is `K`-linear for any `K`-algebra structure on the ring: the scalars are
central. -/
theorem conjRingHom_smul {S K : Type*} [Ring S] [CommSemiring K] [Algebra K S]
    (c ci : S) (hc : c * ci = 1) (hc' : ci * c = 1) (r : K) (y : S) :
    conjRingHom c ci hc hc' (r • y) = r • conjRingHom c ci hc hc' y := by
  rw [conjRingHom_apply, conjRingHom_apply, Algebra.smul_def, Algebra.smul_def]
  rw [← mul_assoc c (algebraMap K S r) y, ← Algebra.commutes r c,
    mul_assoc (algebraMap K S r) c y, mul_assoc (algebraMap K S r) (c * y) ci]

/-- **Conjugation invariance of the division closure (Linnell datum (I2)).**  For a group element
`g : G` and a subgroup `H ≤ G`, conjugation by the group basis element `gen g` carries the
division closure `D H` of `K[H]` inside `U(G)` into the division closure `D (H^g)` of `K[H^g]`. -/
theorem D_conj_mem {G : Type*} [Group G] {K : Type*} [Field K]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (g : G) (H : Subgroup G) {x : E.U} (hx : x ∈ Work.ORBridgeLinnell.D E φK H) :
    (Work.ORBridgeLinnell.gen E g : E.U) * x * ↑((Work.ORBridgeLinnell.gen E g)⁻¹)
      ∈ Work.ORBridgeLinnell.D E φK (H.map (MulAut.conj g)) := by
  let H' : Subgroup G := H.map (MulAut.conj g)
  have hc : (gen E g : E.U) * ↑((gen E g)⁻¹) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc' : ↑((gen E g)⁻¹) * (gen E g : E.U) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let f : E.U →+* E.U := conjRingHom (gen E g : E.U) ↑((gen E g)⁻¹) hc hc'
  have hf : ∀ y : E.U, f y = (gen E g : E.U) * y * ↑((gen E g)⁻¹) :=
    fun y => conjRingHom_apply (gen E g : E.U) ↑((gen E g)⁻¹) hc hc' y
  have hfsmul : ∀ (r : K) (y : E.U), f (r • y) = r • f y :=
    fun r y => conjRingHom_smul (gen E g : E.U) ↑((gen E g)⁻¹) hc hc' r y
  let D' : Subring E.U := D E φK H'
  let C : Subring E.U := D'.comap f
  have hmem : ∀ y : E.U, y ∈ C ↔ f y ∈ D' := fun y => Subring.mem_comap
  have hC : IsDivisionClosed C := by
    intro y hy z hyz
    have hy' : f y ∈ D' := (hmem y).mp hy
    have hmul : f y * f z = 1 := by rw [← map_mul, hyz, map_one]
    exact (hmem z).mpr (isDivisionClosed_D E φK H' (f y) hy' (f z) hmul)
  have hrange : Set.range (toUK E φK H) ⊆ (C : Set E.U) := by
    rintro _ ⟨y, rfl⟩
    refine (hmem (toUK E φK H y)).mpr ?_
    induction y using MonoidAlgebra.induction_on with
    | of m =>
      rw [toUK_of, hf]
      have hgm : g * (m : G) * g⁻¹ ∈ H' :=
        ⟨(m : G), m.2, MulAut.conj_apply g (m : G)⟩
      have key : (gen E g : E.U) * genU E (m : G) * ↑((gen E g)⁻¹)
          = genU E (g * (m : G) * g⁻¹) := by
        rw [gen_apply, gen_inv_apply, genU_apply, genU_apply, ← map_mul, ← map_mul,
          MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one]
      rw [key]
      exact gen_mem_D' E φK hgm
    | add a b ha hb =>
      rw [map_add, map_add]
      exact D'.add_mem ha hb
    | smul r a ha =>
      rw [map_smul, hfsmul, Algebra.smul_def]
      exact D'.mul_mem (algebraMap_mem_D E φK H' r) ha
  have hxC : x ∈ C := (mem_D_iff E φK).mp hx C hrange hC
  have hfx : f x ∈ D' := (hmem x).mp hxC
  rw [hf x] at hfx
  exact hfx

end Work.ORBridgeLinnell

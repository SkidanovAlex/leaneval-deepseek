/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The M1 bridge: from node N5's envelope to node N7's Linnell datum

This file proves the **twelve fields** of `Work.ORLinnell.LinnellDatum K G U` for the ambient
ring `U = U(G)` of node N5's envelope, from the envelope interface
`Work.ORVonNeumann.StarRegularEnvelope G` over `ℂ` and a field embedding `K →+* ℂ` — except for
the two Hughes-free / Ore inputs, which are isolated as the explicit hypothesis structure
`Work.ORBridgeLinnell.HughesFreeInput` (see `Defs.lean` and `README.md`).

The mathematically interesting step is Linnell independence **(I1)/(I1′)**: the envelope's
`EnvelopeInclusion.linnell` is stated for coefficients in `U(H) = (E.sub H).V`, while the Linnell
datum needs it for coefficients in the division closure `D H ⊆ U(G)`.  The two are bridged by the
inclusion `D H ≤ (E.sub H).φ.range`, which follows from the **division closedness of `U(H)` in
`U(G)`**:

* `U(H)` is von Neumann regular (`EnvelopeInclusion.starRegularV`),
* `U(H)` is directly finite, because it carries the faithful Sylvester rank function
  `EnvelopeInclusion.rkV` (`Work.ORBridgeLinnell.directlyFinite_of_faithful`),
* so a right inverse in `U(G)` of an element of `φ(U(H))` lies in `φ(U(H))`
  (`Work.ORBridgeLinnell.isDivisionClosed_range`),
* hence the subring `φ(U(H))` is division closed, and the division closure `D H` of `K[H]` —
  which is contained in it by minimality — is contained in `φ(U(H))`.

## Main results

* `Work.ORBridgeLinnell.D_le_phi_range` — `D H ≤ (E.sub H).φ.range`;
* `Work.ORBridgeLinnell.independence_D`, `...independence'_D` — **(I1)**, **(I1′)**;
* `Work.ORBridgeLinnell.D_conj_mem` — **(I2)** (proved in `D_conj_mem.lean`);
* `Work.ORBridgeLinnell.linnellDatumOf` — the Linnell datum from the envelope, the field embedding
  and the two Hughes-free/Ore inputs;
* `Work.ORBridgeLinnell.linnellDatumOfEnvelope`, `...linBridgeDataOf` — the canonical-instance
  wrappers.
-/
import Mathlib
import Submission.Work.ORBridgeLinnell.Basic
import Submission.Work.ORBridgeLinnell.Defs
import Submission.Work.ORBridgeLinnell.OreField
import Submission.Work.ORBridgeLinnell.isDivisionClosed_range
import Submission.Work.ORBridgeLinnell.directlyFinite_of_faithful
import Submission.Work.ORBridgeLinnell.linnellIndependent_fintype
import Submission.Work.ORBridgeLinnell.D_conj_mem

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORBridgeLinnell

open Work.ORVonNeumann

variable {G : Type*} [Group G] {K : Type*} [Field K]

/-! ## The ambient ring `U(G)` is nontrivial -/

/-- `U(G)` is nontrivial: the faithful rank function takes the value `1` on `1` and `0` on `0`. -/
instance nontrivial_U (E : StarRegularEnvelope G) : Nontrivial E.U where
  exists_pair_ne := ⟨1, 0, fun h => by
    have hm : (1 : Matrix (Fin 1) (Fin 1) E.U) = 0 := by
      ext i j
      fin_cases i; fin_cases j
      simpa using h
    have h1 : E.rk.toFun 1 1 (1 : Matrix (Fin 1) (Fin 1) E.U)
        = E.rk.toFun 1 1 (0 : Matrix (Fin 1) (Fin 1) E.U) := by rw [hm]
    rw [E.rk.map_one, E.rk.map_zero] at h1
    exact one_ne_zero h1⟩

/-! ## The division closedness of `U(H) ⊆ U(G)` -/

/-- **`U(H) = (E.sub H).V` is division closed inside `U(G)`**, i.e. `(E.sub H).φ.range` is closed
under inverses in `U(G)`.  The inputs are von Neumann regularity of `U(H)`
(`EnvelopeInclusion.starRegularV`) and its direct finiteness, which follows from the faithful
Sylvester rank function `EnvelopeInclusion.rkV`. -/
theorem phi_range_divisionClosed (E : StarRegularEnvelope G) (H : Subgroup G) :
    IsDivisionClosed (E.sub H).φ.range :=
  isDivisionClosed_range (E.sub H).φ (E.sub H).φ_injective (E.sub H).starRegularV.1
    (fun a b hab => directlyFinite_of_faithful (E.sub H).rkV (E.sub H).rkV_faithful hab)

/-- **`D H ≤ U(H)`**: the division closure of `K[H]` in `U(G)` is contained in the image of
`U(H)`.  This is the form of Linnell independence needed to transfer the envelope's cosetwise
independence to the Linnell datum. -/
theorem D_le_phi_range (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k)) (H : Subgroup G) :
    D E φK H ≤ (E.sub H).φ.range := by
  refine D_minimal E φK ?_ (phi_range_divisionClosed E H)
  rintro _ ⟨x, rfl⟩
  induction x using MonoidAlgebra.induction_on with
  | of h =>
      rw [toUK_of, genU_apply]
      exact ⟨(E.sub H).ιH (MonoidAlgebra.single h 1), (E.sub H).φ_ι h 1⟩
  | add x y hx hy => rw [map_add]; exact (E.sub H).φ.range.add_mem hx hy
  | smul r x hx =>
      rw [map_smul, Algebra.smul_def]
      refine (E.sub H).φ.range.mul_mem ?_ hx
      rw [hφK r]
      refine ⟨(E.sub H).ιH (MonoidAlgebra.single (1 : ↥H) (φK r)), ?_⟩
      rw [(E.sub H).φ_ι (1 : ↥H) (φK r), Subgroup.coe_one, ← E.ι_algebraMap (φK r)]
      rfl

/-- The image of `K[H]` in `U(G)` lies in any subring containing the group basis of `H` and the
`K`-scalars: the form of the Linnell datum's `minimal` field. -/
theorem toUK_mem_of_mem (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {H : Subgroup G} {A : Subring E.U} (hgen : ∀ h : ↥H, (gen E (h : G) : E.U) ∈ A)
    (hk : ∀ k : K, algebraMap K E.U k ∈ A) :
    Set.range (toUK E φK H) ⊆ (A : Set E.U) := by
  rintro _ ⟨x, rfl⟩
  induction x using MonoidAlgebra.induction_on with
  | of h =>
      rw [toUK_of, genU_apply, ← gen_apply]
      exact hgen h
  | add x y hx hy => rw [map_add]; exact A.add_mem hx hy
  | smul r x hx =>
      rw [map_smul, Algebra.smul_def]
      exact A.mul_mem (hk r) hx

/-! ## Linnell independence -/

/-- **(I1) Linnell independence for the division closure `D H`**, deduced from the envelope's
`EnvelopeInclusion.linnell` via `D H ≤ U(H)` (`D_le_phi_range`). -/
theorem independence_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    (H : Subgroup G) (n : ℕ) (g : Fin n → G)
    (hg : ∀ i j, g i * (g j)⁻¹ ∈ H → i = j) (a : Fin n → E.U)
    (ha : ∀ i, a i ∈ D E φK H) (hsum : ∑ i, a i * (gen E (g i) : E.U) = 0) :
    ∀ i, a i = 0 := by
  choose d hd using fun i => D_le_phi_range E φK hφK H (ha i)
  have hsum' : ∑ i, (E.sub H).φ (d i) * E.ι (MonoidAlgebra.single (g i) 1) = 0 := by
    rw [← hsum, Finset.sum_congr rfl]
    intro i _
    rw [← hd i, gen_apply]
  have h0 := linnellIndependent_fintype H (E.sub H).φ E.ι (E.sub H).linnell g d hg hsum'
  intro i
  rw [← hd i, h0 i, map_zero]

/-- The involution of `U(G)` inverts the group basis: `⋆(gen g) = gen g⁻¹`. -/
@[simp]
theorem star_gen (E : StarRegularEnvelope G) (g : G) :
    star ((gen E g : E.Uˣ) : E.U) = ((gen E g⁻¹ : E.Uˣ) : E.U) := by
  rw [gen_apply, ← E.ι_star, MonoidAlgebra.star_single, star_one, gen_apply]

/-- **(I1′) Linnell independence, coefficients on the right**, deduced from **(I1)** applied to the
star of the coefficient family.  The involution of `U(G)` and of `ℂ[G]` (node N5) turn left
cosets into right cosets: `⋆(gen g) = gen g⁻¹`. -/
theorem independence'_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    (H : Subgroup G) (n : ℕ) (g : Fin n → G)
    (hg : ∀ i j, (g i)⁻¹ * (g j) ∈ H → i = j) (a : Fin n → E.U)
    (ha : ∀ i, a i ∈ D E φK H) (hsum : ∑ i, (gen E (g i) : E.U) * a i = 0) :
    ∀ i, a i = 0 := by
  choose d hd using fun i => D_le_phi_range E φK hφK H (ha i)
  have hstar : ∑ i, star ((gen E (g i) : E.U) * a i) = 0 := by
    have h0 : star (∑ i, (gen E (g i) : E.U) * a i) = star 0 := by rw [hsum]
    rwa [star_sum, star_zero] at h0
  have hsum' : ∑ i, (E.sub H).φ (star (d i)) * E.ι (MonoidAlgebra.single ((g i)⁻¹) 1) = 0 := by
    rw [← hstar, Finset.sum_congr rfl]
    intro i _
    rw [star_mul, ← hd i, ← (E.sub H).φ_star, star_gen, ← gen_apply]
  have hg' : ∀ i j : Fin n, (g i)⁻¹ * ((g j)⁻¹)⁻¹ ∈ H → i = j := by
    intro i j hij
    exact hg i j (by simpa using hij)
  have h0 := linnellIndependent_fintype H (E.sub H).φ E.ι (E.sub H).linnell
    (fun i => (g i)⁻¹) (fun i => star (d i)) hg' hsum'
  intro i
  have h1 : star (d i) = 0 := h0 i
  rw [← hd i, ← star_star (d i), h1, star_zero, map_zero]

/-! ## The Linnell datum -/

/-- **The M1 bridge.**  A `LinnellDatum K G U(G)` built from

* node N5's envelope `E : StarRegularEnvelope G` (over `ℂ`),
* a field embedding `φK : K →+* ℂ` and the induced `K`-algebra structure on `U(G)`
  (hypothesis `hφK`),
* the two Hughes-free / Ore inputs of node N6 (`hdiv`, `hfrac`), see
  `Work.ORBridgeLinnell.HughesFreeInput`.

Every other field of the Linnell datum is proved here. -/
noncomputable def linnellDatumOf (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    (hdiv : ∀ H : Subgroup G, IsMulTorsionFree H → ∀ x : ↥(D E φK H), x ≠ 0 → IsUnit x)
    (hfrac : ∀ (N Γ : Subgroup G), N ≤ Γ → IsMulTorsionFree Γ → Work.ORLinnell.IsExtensionByZ N Γ →
      ∀ e ∈ (D E φK Γ : Set E.U), ∃ a ∈ Subring.closure (((D E φK N : Subring E.U) : Set E.U) ∪
          Set.range (fun γ : Γ => (gen E (γ : G) : E.U))),
        ∃ t ∈ Subring.closure (((D E φK N : Subring E.U) : Set E.U) ∪
          Set.range (fun γ : Γ => (gen E (γ : G) : E.U))), t ≠ 0 ∧ e * t = a) :
    Work.ORLinnell.LinnellDatum K G E.U where
  gen := gen E
  gen_injective := gen_injective E
  D := fun H => D E φK H
  gen_mem := fun H h => gen_mem_D E φK H h
  algebraMap_mem := fun H k => algebraMap_mem_D E φK H k
  isDivisionClosed := fun H => isDivisionClosed_D E φK H
  minimal := fun H A hgen hk hA => D_minimal E φK (toUK_mem_of_mem E φK hgen hk) hA
  independence := fun H n g hg a ha hsum => independence_D E φK hφK H n g hg a ha hsum
  independence' := fun H n g hg a ha hsum => independence'_D E φK hφK H n g hg a ha hsum
  conjugation := fun g H x hx => D_conj_mem E φK g H hx
  division_of_torsionFree := fun H htf => hdiv H htf
  ore_field_unit := fun N Γ hN htf hφ t ht htne =>
    ore_field_unit_of_division E φK hdiv N Γ hN htf hφ ht htne
  ore_field_frac := fun N Γ hN htf hφ => hfrac N Γ hN htf hφ

/-- **The M1 bridge, in the canonical form in which the assembly consumes it**: from the envelope
`E`, the field embedding `φK` and the Hughes-free / Ore input `hin`, produce the Linnell datum for
the canonical `K`-algebra structure `kAlgebra E φK` on `U(G)`. -/
noncomputable def linnellDatumOfEnvelope (E : StarRegularEnvelope G) (φK : K →+* ℂ)
    (hin : HughesFreeInput K G E φK) :
    letI := kAlgebra E φK
    Work.ORLinnell.LinnellDatum K G E.U := by
  letI := kAlgebra E φK
  exact linnellDatumOf E φK (fun _ => rfl) (fun H htf => hin.div_of_torsionFree H htf)
    (fun N Γ hN htf hφ => hin.ore_field_frac N Γ hN htf hφ)

/-- **The packaged output of the M1 bridge**: the `U`/`datum` fields of
`Work.ORAssembly.RingInputs`. -/
noncomputable def linBridgeDataOf (E : StarRegularEnvelope G) (φK : K →+* ℂ)
    (hin : HughesFreeInput K G E φK) : LinBridgeData K G where
  U := E.U
  ringU := E.ringU
  nontrivialU := nontrivial_U E
  algebraU := kAlgebra E φK
  datum := linnellDatumOfEnvelope E φK hin

end Work.ORBridgeLinnell

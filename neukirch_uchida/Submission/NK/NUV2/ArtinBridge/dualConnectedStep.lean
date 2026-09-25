import Mathlib
import Submission.NK.RankTheoryDeep.CharModule

/-!
# The dual of the idèle class group depends only on `C_K ⧸ C_K⁰`

This file proves

`NK.NUV2.ArtinBridge.dualConnectedStep`,

the **connected-component step** of the Artin-duality bridge for `C_K = 𝕀 K ⧸ Kˣ`:

`Dual C_K ℓ ≃ₗ[ℤ_ℓ] Dual (C_K ⧸ (C_K)⁰) ℓ`,

where `(C_K)⁰ = Subgroup.connectedComponentOfOne C_K` is the connected component of the identity
and `NK.Reconstruct.Dual G ℓ = Hom_cts(G, ℤ_ℓ)` is the continuous dual
(`Submission/Work/Reconstruct/GammaDual.lean`).

The mathematical content is completely general and does not use anything about `C_K`: `ℤ_ℓ` is
totally disconnected (`TotallyDisconnectedSpace (ℤ_ℓ)`, supplied by the `IsUltrametricDist` /
`TotallySeparatedSpace` instance), so the image of the connected set `(G)⁰` under a continuous
homomorphism `f : G → ℤ_ℓ` is a connected subset of a totally disconnected space, hence a point;
as `1 ↦ 0` the image is `{0}`.  Consequently every continuous `f : G →* ℤ_ℓ` kills `(G)⁰`, so it
descends to the quotient `G ⧸ (G)⁰` (`QuotientAddGroup.lift`, applied to `Additive G`), and
conversely every continuous homomorphism of the quotient pulls back along the quotient map.  The
two constructions are inverse to each other, and are `ℤ_ℓ`-linear, giving the advertised linear
equivalence.

Everything is proved for an arbitrary `CommGroup` `G` with a topological group structure, and then
specialised to `G = C_K`.
-/

namespace NK.NUV2.ArtinBridge

open NK.Reconstruct

/-! ## The general statement for a topological abelian group -/

namespace DualConnectedStepAux

section General

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **A continuous homomorphism `G → ℤ_ℓ` kills the connected component of the identity.**
The image of the connected set `(G)⁰` is connected in the totally disconnected group `ℤ_ℓ`, hence
a single point, and it contains `f 1 = 0`. -/
theorem vanish (f : Dual G ℓ) :
    ∀ x ∈ Subgroup.connectedComponentOfOne G, f.1 (Additive.ofMul x) = 0 := by
  intro x hx
  have hcont : Continuous (fun y : G => f.1 (Additive.ofMul y)) := f.2
  have h := hcont.mapsTo_connectedComponent (1 : G)
  have h1 : f.1 (Additive.ofMul (1 : G)) = 0 := map_zero f.1
  have hx' : f.1 (Additive.ofMul x) ∈ connectedComponent (f.1 (Additive.ofMul 1)) := h hx
  rw [h1, connectedComponent_eq_singleton] at hx'
  simpa using hx'

/-- The additive form of `vanish`: the connected component of the identity is contained in the
kernel of `f`. -/
theorem vanish_ker (f : Dual G ℓ) :
    (Subgroup.connectedComponentOfOne G).toAddSubgroup ≤ f.1.ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  have hx' : x.toMul ∈ Subgroup.connectedComponentOfOne G := hx
  have := vanish f x.toMul hx'
  rwa [← ofMul_toMul x] at this

/-- The descent of a continuous homomorphism `G → ℤ_ℓ` to `G ⧸ (G)⁰` is continuous: the quotient
map is a quotient map and the composite with it is `f`. -/
theorem continuous_lift_aux (f : Dual G ℓ) :
    Continuous (QuotientAddGroup.lift (Subgroup.connectedComponentOfOne G).toAddSubgroup f.1
      (vanish_ker f)) := by
  rw [(QuotientAddGroup.isQuotientMap_mk
    (Subgroup.connectedComponentOfOne G).toAddSubgroup).continuous_iff]
  change Continuous (fun x : Additive G =>
    QuotientAddGroup.lift (Subgroup.connectedComponentOfOne G).toAddSubgroup f.1 (vanish_ker f) x)
  have heq : (fun x : Additive G =>
      QuotientAddGroup.lift (Subgroup.connectedComponentOfOne G).toAddSubgroup f.1 (vanish_ker f) x)
        = ⇑f.1 := by
    funext x
    exact QuotientAddGroup.lift_mk' (Subgroup.connectedComponentOfOne G).toAddSubgroup
      (vanish_ker f) x
  rw [heq]
  exact f.2

/-- **The forward map**: a continuous homomorphism of `G` that kills `(G)⁰` descends to a
continuous homomorphism of `G ⧸ (G)⁰`. -/
noncomputable def fwd (f : Dual G ℓ) : Dual (G ⧸ Subgroup.connectedComponentOfOne G) ℓ :=
  ⟨QuotientAddGroup.lift (Subgroup.connectedComponentOfOne G).toAddSubgroup f.1 (vanish_ker f),
    continuous_lift_aux f⟩

/-- The defining property of `fwd`, on representatives. -/
theorem fwd_apply_mk (f : Dual G ℓ) (x : G) :
    (fwd f).1 (Additive.ofMul (QuotientGroup.mk (s := Subgroup.connectedComponentOfOne G) x))
      = f.1 (Additive.ofMul x) :=
  QuotientAddGroup.lift_mk' (Subgroup.connectedComponentOfOne G).toAddSubgroup (vanish_ker f)
    (Additive.ofMul x)

/-- The quotient map is continuous (in the group form needed by `dualMap`). -/
theorem continuous_quotientGroup_mk' :
    Continuous ⇑(QuotientGroup.mk' (Subgroup.connectedComponentOfOne G)) := by
  rw [QuotientGroup.coe_mk']
  exact QuotientGroup.continuous_mk

/-- **The backward map**: precomposition with the quotient map `G → G ⧸ (G)⁰`. -/
noncomputable def bwd (g : Dual (G ⧸ Subgroup.connectedComponentOfOne G) ℓ) : Dual G ℓ :=
  dualMap ℓ (QuotientGroup.mk' (Subgroup.connectedComponentOfOne G)) continuous_quotientGroup_mk' g

/-- `bwd` is a left inverse of `fwd`. -/
theorem bwd_fwd (f : Dual G ℓ) : bwd (fwd f) = f := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  rw [← ofMul_toMul x]
  exact fwd_apply_mk f x.toMul

/-- `bwd` is injective, being the dual of the surjection `G → G ⧸ (G)⁰`. -/
theorem bwd_injective : Function.Injective (bwd (G := G) (ℓ := ℓ)) :=
  dualMap_injective_of_surjective ℓ (QuotientGroup.mk' (Subgroup.connectedComponentOfOne G))
    continuous_quotientGroup_mk' (QuotientGroup.mk'_surjective _)

/-- `bwd` is a right inverse of `fwd`. -/
theorem fwd_bwd (g : Dual (G ⧸ Subgroup.connectedComponentOfOne G) ℓ) : fwd (bwd g) = g :=
  bwd_injective (bwd_fwd (bwd g))

/-- `fwd` is injective. -/
theorem fwd_injective : Function.Injective (fwd (G := G) (ℓ := ℓ)) := fun f g h => by
  rw [← bwd_fwd f, h, bwd_fwd g]

/-- `fwd` is surjective. -/
theorem fwd_surjective : Function.Surjective (fwd (G := G) (ℓ := ℓ)) :=
  fun g => ⟨bwd g, fwd_bwd g⟩

/-- `fwd` is additive. -/
theorem fwd_add (f g : Dual G ℓ) : fwd (f + g) = fwd f + fwd g := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s := Subgroup.connectedComponentOfOne G) x.toMul
  rw [show x = Additive.ofMul (QuotientGroup.mk (s := Subgroup.connectedComponentOfOne G) y) from by
    rw [hy, ofMul_toMul]]
  simp only [AddSubgroup.coe_add, AddMonoidHom.add_apply, fwd_apply_mk]

/-- `fwd` is `ℤ_ℓ`-linear. -/
theorem fwd_smul (c : PadicInt ℓ) (f : Dual G ℓ) : fwd (c • f) = c • fwd f := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s := Subgroup.connectedComponentOfOne G) x.toMul
  rw [show x = Additive.ofMul (QuotientGroup.mk (s := Subgroup.connectedComponentOfOne G) y) from by
    rw [hy, ofMul_toMul]]
  simp only [NK.RankTheoryDeep.smul_dual_apply, fwd_apply_mk]

/-- `fwd` as a `ℤ_ℓ`-linear map. -/
noncomputable def fwdLin :
    Dual G ℓ →ₗ[PadicInt ℓ] Dual (G ⧸ Subgroup.connectedComponentOfOne G) ℓ where
  toFun := fwd
  map_add' := fwd_add
  map_smul' := fwd_smul

/-- **The connected-component step in general form**:
`Dual G ℓ ≃ₗ[ℤ_ℓ] Dual (G ⧸ (G)⁰) ℓ` for every topological abelian group `G`. -/
noncomputable def dualConnectedStepEquiv :
    Dual G ℓ ≃ₗ[PadicInt ℓ] Dual (G ⧸ Subgroup.connectedComponentOfOne G) ℓ :=
  LinearEquiv.ofBijective fwdLin ⟨fwd_injective, fwd_surjective⟩

end General

end DualConnectedStepAux

/-- **The connected-component step of the Artin bridge.**  The continuous dual
`Hom_cts(C_K, ℤ_ℓ)` of the idèle class group is (linearly) the same as the continuous dual of the
profinite-quotient `C_K ⧸ C_K⁰`: a continuous homomorphism of `C_K` into the totally disconnected
group `ℤ_ℓ` kills the connected component of the identity. -/
theorem dualConnectedStep (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty ((NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K) ℓ) ≃ₗ[PadicInt ℓ]
      (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K ⧸
        Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) ℓ)) :=
  ⟨DualConnectedStepAux.dualConnectedStepEquiv⟩

end NK.NUV2.ArtinBridge

import Mathlib

/-!
# `V ⧸ V ^ ℓ` is infinite iff `G ⧸ G ^ ℓ` is, for `V ≤ G` of finite index

Throughout, `G` is a commutative group, `V ≤ G` a subgroup of finite index `n`, and `ℓ : ℕ`.
Writing `G ^ ℓ` for the image of the `ℓ`-th power map `powMonoidHom ℓ : G →* G` and `V ^ ℓ` for
the corresponding subgroup of `V`, we prove

`Infinite (V ⧸ V ^ ℓ) ↔ Infinite (G ⧸ G ^ ℓ)`.

The mathematical content is an *almost*-isomorphism between the two quotients.  Let `M = G ^ ℓ`
and `N = V ^ ℓ` (viewed as a subgroup of `G` via `V.subtype`).  There is a map

`φ : {x : G | x ^ ℓ ∈ V} ⟶ V ⧸ N,  x ↦ x ^ ℓ · N`,

which is a homomorphism because `G` is commutative, and whose image is `(V ∩ M) · N / N`.  Its
kernel contains `V`, so `φ` factors through the quotient of `{x | x ^ ℓ ∈ V}` by `V`; that quotient
is a subgroup of `G ⧸ V` (consisting of the elements of order dividing `ℓ`), hence finite, because
`V` has finite index.  Therefore `(V ∩ M) / N` is finite — this is the key point
(`relIndex_powRange_ne_zero` below).

Indices then give the equivalence:
`[V : N] = [V : V ∩ M] · [(V ∩ M) : N]` and `[G : M] = [G : V · M] · [V : V ∩ M]`, with the outer
factors finite and nonzero.  So `[V : N]` is finite exactly when `[V : V ∩ M]` is, exactly when
`[G : M]` is, i.e. exactly when `G ⧸ G ^ ℓ` is finite.

No hypothesis on `ℓ` is needed: for `ℓ = 0` (resp. `ℓ = 1`) both `G ^ ℓ` and `V ^ ℓ` are trivial
(resp. everything), and the statement reduces to "`V` is finite iff `G` is", which holds for a
subgroup of finite index.
-/

namespace NK.LocalCFT.Units

/-- **The kernel of `x ↦ x ^ ℓ` on the ℓ-th powers lying in `V` is finite.**

Let `G` be commutative, `V ≤ G` of finite index and `ℓ : ℕ`.  Then the ℓ-th powers of `V` have
finite index in `V ∩ G ^ ℓ`; equivalently, the subgroup `(V ∩ G ^ ℓ) / V ^ ℓ` is finite.  In the
notation of the proof: `(V ^ ℓ).relIndex (G ^ ℓ ⊓ V) ≠ 0`.

Indeed, `H = {x : G | x ^ ℓ ∈ V}` contains `V` with finite quotient `H / V ≤ G / V`, and the map
`H → V ⧸ V ^ ℓ`, `x ↦ x ^ ℓ · V ^ ℓ` has image `(V ∩ G ^ ℓ) / V ^ ℓ` and kernel containing `V`. -/
lemma relIndex_powRange_ne_zero {G : Type*} [CommGroup G] (V : Subgroup G) (hV : V.FiniteIndex)
    (ℓ : ℕ) :
    ((powMonoidHom ℓ : ↥V →* ↥V).range).relIndex
      (((powMonoidHom ℓ : G →* G).range).subgroupOf V) ≠ 0 := by
  classical
  set N : Subgroup ↥V := (powMonoidHom ℓ : ↥V →* ↥V).range with hNdef
  set M : Subgroup G := (powMonoidHom ℓ : G →* G).range with hMdef
  set W : Subgroup ↥V := M.subgroupOf V with hWdef
  set H : Subgroup G := V.comap (powMonoidHom ℓ : G →* G) with hHdef
  have hVH : V ≤ H := by
    intro v hv
    rw [hHdef, Subgroup.mem_comap, powMonoidHom_apply]
    exact V.pow_mem hv ℓ
  have hVidx : V.index ≠ 0 := Subgroup.finiteIndex_iff.mp hV
  have hrelVH : (V.subgroupOf H).index ≠ 0 := by
    show V.relIndex H ≠ 0
    have h := Subgroup.relIndex_mul_index hVH
    intro hz
    exact hVidx (by rw [← h, hz, zero_mul])
  have hfinH : Finite (↥H ⧸ (V.subgroupOf H)) := Subgroup.index_ne_zero_iff_finite.mp hrelVH
  -- the map `x ↦ x ^ ℓ` from `H` to `V`, followed by the projection to `V ⧸ N`
  let φ : ↥H →* (↥V ⧸ N) :=
    (QuotientGroup.mk' N).comp
      (MonoidHom.codRestrict ((powMonoidHom ℓ : G →* G).comp H.subtype) V (fun h => h.2))
  have hφker : V.subgroupOf H ≤ φ.ker := by
    intro v hv
    rw [MonoidHom.mem_ker]
    have hmem : (⟨(powMonoidHom ℓ : G →* G) (v : G), v.2⟩ : ↥V) ∈ N := by
      rw [hNdef]
      refine MonoidHom.mem_range.mpr ⟨⟨(v : G), hv⟩, ?_⟩
      ext
      simp [powMonoidHom_apply]
    show QuotientGroup.mk' N (⟨(powMonoidHom ℓ : G →* G) (v : G), v.2⟩ : ↥V) = 1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  let ψ : (↥H ⧸ (V.subgroupOf H)) →* (↥V ⧸ N) := QuotientGroup.lift (V.subgroupOf H) φ hφker
  have hrange : φ.range = ψ.range := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      refine ⟨QuotientGroup.mk' (V.subgroupOf H) h, ?_⟩
      rw [QuotientGroup.mk'_apply]
      exact QuotientGroup.lift_mk' (V.subgroupOf H) hφker h
    · rintro y ⟨x, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf H) x
      refine ⟨h, ?_⟩
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.lift_mk' (V.subgroupOf H) hφker h).symm
  have hfinψ : Finite ↥ψ.range :=
    haveI := hfinH
    Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hfinφ : Finite ↥φ.range := hrange ▸ hfinψ
  -- the image of `φ` is `(V ∩ G ^ ℓ) / V ^ ℓ`
  have hφrange_eq : φ.range = W.map (QuotientGroup.mk' N) := by
    apply le_antisymm
    · rintro y ⟨h, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨(powMonoidHom ℓ : G →* G) (h : G), h.2⟩, ?_, rfl⟩
      rw [hWdef, Subgroup.mem_subgroupOf, hMdef]
      exact MonoidHom.mem_range.mpr ⟨(h : G), rfl⟩
    · rintro y ⟨w, hw, rfl⟩
      simp only [SetLike.mem_coe] at hw
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hw
      refine ⟨⟨g, ?_⟩, ?_⟩
      · rw [hHdef, Subgroup.mem_comap, hg]
        exact w.2
      · show QuotientGroup.mk' N (⟨(powMonoidHom ℓ : G →* G) g, _⟩ : ↥V) =
          QuotientGroup.mk' N w
        congr 1
        exact Subtype.ext hg
  have hfinW : Finite ↥(W.map (QuotientGroup.mk' N)) := hφrange_eq ▸ hfinφ
  -- so the quotient `W ⧸ N` is finite
  have hker : ((QuotientGroup.mk' N).comp W.subtype).ker = N.subgroupOf W := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hfinrange : Finite ↥(((QuotientGroup.mk' N).comp W.subtype).range) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hfinW
  have hfinquot : Finite (↥W ⧸ (N.subgroupOf W)) := by
    rw [← hker]
    exact (QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' N).comp W.subtype)).toEquiv.finite_iff.mpr
      hfinrange
  have := hfinquot
  exact Subgroup.index_ne_zero_of_finite

/-- **`V ⧸ V ^ ℓ` is infinite if and only if `G ⧸ G ^ ℓ` is**, for `V ≤ G` of finite index.

See the module docstring for the proof sketch: the quotient `(V ∩ G ^ ℓ) / V ^ ℓ` is finite
(`relIndex_powRange_ne_zero`), and index multiplicativity in the towers `V ^ ℓ ≤ V ∩ G ^ ℓ ≤ V ≤ G`
and `G ^ ℓ ≤ V · G ^ ℓ ≤ G` gives the result. -/
theorem infinite_quot_powSubgroup_iff {G : Type*} [CommGroup G] (V : Subgroup G)
    (hV : V.FiniteIndex) (ℓ : ℕ) :
    Infinite (↥V ⧸ (powMonoidHom ℓ : ↥V →* ↥V).range) ↔
      Infinite (G ⧸ (powMonoidHom ℓ : G →* G).range) := by
  classical
  set N : Subgroup ↥V := (powMonoidHom ℓ : ↥V →* ↥V).range with hNdef
  set M : Subgroup G := (powMonoidHom ℓ : G →* G).range with hMdef
  have hVidx : V.index ≠ 0 := Subgroup.finiteIndex_iff.mp hV
  -- `V ^ ℓ`, viewed inside `G`, lies in `G ^ ℓ ⊓ V`
  have hNN' : N.map V.subtype ≤ M ⊓ V := by
    rintro x ⟨v, hv, rfl⟩
    refine ⟨?_, v.2⟩
    rw [hNdef] at hv
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hv
    rw [hMdef]
    refine MonoidHom.mem_range.mpr ⟨(w : G), ?_⟩
    simpa [powMonoidHom_apply] using congrArg V.subtype hw
  have e1 : N.index ≠ 0 ↔ (N.map V.subtype).index ≠ 0 := by
    rw [Subgroup.index_map_subtype (H := V) N, mul_ne_zero_iff]
    exact ⟨fun h => ⟨h, hVidx⟩, fun h => h.1⟩
  have e2 : (N.map V.subtype).index ≠ 0 ↔
      (N.map V.subtype).relIndex (M ⊓ V) ≠ 0 ∧ (M ⊓ V).index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index hNN', mul_ne_zero_iff]
  have htop : (M ⊔ V).index ≠ 0 :=
    Nat.pos_iff_ne_zero.mp
      (Nat.pos_of_dvd_of_pos (Subgroup.index_dvd_of_le (le_sup_right : V ≤ M ⊔ V))
        (Nat.pos_of_ne_zero hVidx))
  have hsup : M.relIndex (M ⊔ V) = M.relIndex V := by
    rw [sup_comm]
    exact Subgroup.relIndex_sup_right V M
  have e3 : (M ⊓ V).index ≠ 0 ↔ M.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (inf_le_right : M ⊓ V ≤ V), mul_ne_zero_iff,
      Subgroup.inf_relIndex_right, ← Subgroup.relIndex_mul_index (le_sup_left : M ≤ M ⊔ V),
      hsup, mul_ne_zero_iff]
    exact ⟨fun h => ⟨h.1, htop⟩, fun h => ⟨h.1, hVidx⟩⟩
  have hcrux : (N.map V.subtype).relIndex (M ⊓ V) ≠ 0 := by
    rw [← Subgroup.subgroupOf_map_subtype M V,
      Subgroup.relIndex_map_map_of_injective N (M.subgroupOf V) V.subtype_injective]
    exact relIndex_powRange_ne_zero V hV ℓ
  have key : N.index ≠ 0 ↔ M.index ≠ 0 :=
    e1.trans (e2.trans (by
      rw [e3]
      exact ⟨fun h => h.2, fun h => ⟨hcrux, h⟩⟩))
  have hbig : N.index = 0 ↔ M.index = 0 := by
    rw [← not_not (a := N.index = 0), ← not_not (a := M.index = 0)]
    exact not_congr key
  rw [← Subgroup.index_eq_zero_iff_infinite (H := N),
    ← Subgroup.index_eq_zero_iff_infinite (H := M)]
  exact hbig

end NK.LocalCFT.Units

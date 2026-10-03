import Mathlib
import Submission.Work.Horn.isCoveringMapOn_restrictToPreimage
import Submission.Work.BasinSC.cover_basic

/-!
# The component of the preimage of a simply connected set under a covering off `{0, v}`

Let `g : ℂ → ℂ` be a covering map on the twice punctured plane `ℂ ∖ {0, v}` *restricted to* the
domain `D` (i.e. `IsCoveringMapOn (g|D) {ζ | ζ ≠ 0 ∧ ζ ≠ v}`), and let `V` be a nonempty open
simply connected subset of `ℂ` avoiding both `0` and `v`.  Then every connected component `W` of
`D ∩ g ⁻¹' V` is mapped homeomorphically onto `V` by `g`: `g` is injective on `W`, `V ⊆ g '' W`,
`g` is proper on `W` over `V`, and `W` is simply connected.

The proof is the standard one.  Since `V` is simply connected and locally path connected, the
identity of `V` lifts through the covering to a continuous section `F : V → D` of `g` with
`F (g x) = x`; its range is a connected subset of `D ∩ g ⁻¹' V` containing `x`, so it lies in the
component `W`, giving `V ⊆ g '' W`.  The maps `id` and `F ∘ g` on `W` are two continuous lifts of
`g|W` to the total space of the restricted covering which agree at the point `x`; since `W` is
connected the covering is separated, so they coincide (`IsCoveringMap.eq_of_comp_eq`).  That is the
identity `z = F (g z)` on `W`; it yields injectivity, properness over `V` (the preimage of a
compact `K ⊆ V` is the continuous image of `K` under `F`), and the homeomorphism `W ≅ V`
(inverse to `g`) which transfers simple connectivity.
-/

namespace Work.Horn.HB

open Set

theorem component_homeo_of_covering_vnotin {g : ℂ → ℂ} {D V : Set ℂ} {v x : ℂ} {W : Set ℂ}
    (hVo : IsOpen V) (hVne : V.Nonempty) (hVsc : SimplyConnectedSpace ↥V)
    (h0V : (0 : ℂ) ∉ V) (hvV : v ∉ V)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hxD : x ∈ D) (hxV : g x ∈ V) (hW : W = connectedComponentIn (D ∩ g ⁻¹' V) x) :
    Set.InjOn g W ∧ V ⊆ g '' W ∧ (∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K)) ∧
      SimplyConnectedSpace ↥W := by
  -- `V` lies in the set over which `g` is a covering map, so we may restrict the covering to `V`
  have hVS : V ⊆ {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} := by
    intro y hy
    refine ⟨?_, ?_⟩
    · intro h; rw [h] at hy; exact h0V hy
    · intro h; rw [h] at hy; exact hvV hy
  have hcovV : IsCoveringMapOn (fun z : ↥D => g z) V := hcov.mono hVS
  haveI : SimplyConnectedSpace ↥V := hVsc
  haveI : LocallyPathConnectedSpace ↥V := hVo.locallyPathConnectedSpace
  -- the identity of `V` lifts through the covering to a section `F` of `g` with `F (g x) = x`
  obtain ⟨F, ⟨hF0, hFg⟩, -⟩ := hcovV.existsUnique_continuousMap_lifts
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, ℂ)) (a₀ := ⟨g x, hxV⟩) (e₀ := ⟨x, hxD⟩)
    rfl (fun a => a.2)
  have hpt : ∀ y : ↥V, g ((F y : ↥D) : ℂ) = (y : ℂ) := fun y => congr_fun hFg y
  have hWsub : W ⊆ D ∩ g ⁻¹' V := by rw [hW]; exact connectedComponentIn_subset _ _
  -- `W` is connected
  haveI : PreconnectedSpace ↥W := by
    rw [hW]
    exact (isPreconnected_iff_preconnectedSpace).mp isPreconnected_connectedComponentIn
  -- the range of `F` is a connected subset of `D ∩ g ⁻¹' V` containing `x`, hence lies in `W`
  have hFW : ∀ y : ↥V, ((F y : ↥D) : ℂ) ∈ W := by
    have hpre : IsPreconnected (Set.range (fun y : ↥V => ((F y : ↥D) : ℂ))) :=
      isPreconnected_range (continuous_subtype_val.comp F.continuous)
    have hsub : Set.range (fun y : ↥V => ((F y : ↥D) : ℂ)) ⊆ D ∩ g ⁻¹' V := by
      rintro _ ⟨y, rfl⟩
      refine ⟨(F y).2, ?_⟩
      show g ((F y : ↥D) : ℂ) ∈ V
      rw [hpt y]
      exact y.2
    have hmem : x ∈ Set.range (fun y : ↥V => ((F y : ↥D) : ℂ)) :=
      ⟨⟨g x, hxV⟩, by show ((F ⟨g x, hxV⟩ : ↥D) : ℂ) = x; rw [hF0]⟩
    have hrange : Set.range (fun y : ↥V => ((F y : ↥D) : ℂ)) ⊆ W := by
      rw [hW]
      exact IsPreconnected.subset_connectedComponentIn hpre hmem hsub
    exact fun y => hrange ⟨y, rfl⟩
  -- the two maps `id` and `F ∘ g` on `W`, as maps into the total space of the restricted covering
  have hinc : Continuous (fun z : ↥W => (⟨z.1, (hWsub z.2).1⟩ : ↥D)) :=
    Continuous.subtype_mk continuous_subtype_val _
  have hgcont : Continuous (fun z : ↥W => g z.1) := by
    rw [continuous_iff_continuousAt]
    intro z
    have h1 : ContinuousAt (fun w : ↥D => g w) (⟨z.1, (hWsub z.2).1⟩ : ↥D) :=
      hcovV.continuousAt (hWsub z.2).2
    have h2 : ContinuousAt (fun z : ↥W => (⟨z.1, (hWsub z.2).1⟩ : ↥D)) z := hinc.continuousAt
    have h3 : ContinuousAt ((fun w : ↥D => g w) ∘
        (fun z : ↥W => (⟨z.1, (hWsub z.2).1⟩ : ↥D))) z :=
      ContinuousAt.comp h1 h2
    exact h3
  let u₁ : ↥W → ↥((fun z : ↥D => g z) ⁻¹' V) :=
    fun z => ⟨⟨z.1, (hWsub z.2).1⟩, (hWsub z.2).2⟩
  let u₂ : ↥W → ↥((fun z : ↥D => g z) ⁻¹' V) :=
    fun z => ⟨F ⟨g z.1, (hWsub z.2).2⟩, by
      show g ((F ⟨g z.1, (hWsub z.2).2⟩ : ↥D) : ℂ) ∈ V
      rw [hpt]
      exact (hWsub z.2).2⟩
  have hu₁ : Continuous u₁ := Continuous.subtype_mk hinc _
  have hu₂ : Continuous u₂ := by
    refine Continuous.subtype_mk (F.continuous.comp ?_) _
    exact Continuous.subtype_mk hgcont _
  -- the restricted covering (a genuine `IsCoveringMap` with total space `g ⁻¹' V`)
  have hP : IsCoveringMap (V.restrictPreimage (fun z : ↥D => g z)) :=
    hcovV.isCoveringMap_restrictPreimage
  have heq : (V.restrictPreimage (fun z : ↥D => g z)) ∘ u₁ =
      (V.restrictPreimage (fun z : ↥D => g z)) ∘ u₂ := by
    funext z
    apply Subtype.ext
    show g z.1 = g ((F ⟨g z.1, (hWsub z.2).2⟩ : ↥D) : ℂ)
    rw [hpt]
  have hxW : x ∈ W := by rw [hW]; exact mem_connectedComponentIn ⟨hxD, hxV⟩
  have ha : u₁ ⟨x, hxW⟩ = u₂ ⟨x, hxW⟩ := by
    apply Subtype.ext
    show (⟨x, hxD⟩ : ↥D) = F ⟨g x, hxV⟩
    rw [hF0]
  have hcomp_eq : u₁ = u₂ := IsCoveringMap.eq_of_comp_eq hP hu₁ hu₂ heq ⟨x, hxW⟩ ha
  -- **the key identity**: on `W`, `z = F (g z)`
  have hkey : ∀ z : ↥W, (z : ℂ) = ((F ⟨g z.1, (hWsub z.2).2⟩ : ↥D) : ℂ) := by
    intro z
    have h1 := congr_fun hcomp_eq z
    exact congrArg (fun w : ↥((fun z : ↥D => g z) ⁻¹' V) => ((w.1 : ↥D) : ℂ)) h1
  -- the same identity with the value `y = g z` and the proof component forgotten
  have hkeyW : ∀ (z : ℂ) (hz : z ∈ W) (y : ↥V), g z = (y : ℂ) → z = ((F y : ↥D) : ℂ) := by
    intro z hz y hy
    have h1 := hkey ⟨z, hz⟩
    have h2 : (⟨g z, (hWsub hz).2⟩ : ↥V) = y := Subtype.ext hy
    rw [h2] at h1
    exact h1
  -- injectivity
  have hinj : Set.InjOn g W := by
    intro z₁ hz₁ z₂ hz₂ hgg
    rw [hkeyW z₁ hz₁ ⟨g z₁, (hWsub hz₁).2⟩ rfl,
      hkeyW z₂ hz₂ ⟨g z₂, (hWsub hz₂).2⟩ rfl]
    exact congrArg (fun y : ↥V => ((F y : ↥D) : ℂ)) (Subtype.ext hgg)
  -- surjectivity
  have hsurj : V ⊆ g '' W := by
    intro y hy
    exact ⟨((F ⟨y, hy⟩ : ↥D) : ℂ), hFW ⟨y, hy⟩, by
      show g ((F ⟨y, hy⟩ : ↥D) : ℂ) = (⟨y, hy⟩ : ↥V)
      rw [hpt]⟩
  -- properness over `V`: the preimage of a compact `K ⊆ V` is the continuous image of `K` under `F`
  have hcompact : ∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K) := by
    intro K hKV hK
    have hFr : Continuous (fun y : ↥V => ((F y : ↥D) : ℂ)) :=
      continuous_subtype_val.comp F.continuous
    have hK' : IsCompact (Set.range (fun k : ↥K => (((F (⟨k.1, hKV k.2⟩ : ↥V)) : ↥D) : ℂ))) := by
      haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
      exact isCompact_range (hFr.comp (by fun_prop))
    convert hK' using 1
    ext z
    constructor
    · rintro ⟨hzW, hzK⟩
      exact ⟨⟨g z, hzK⟩, (hkeyW z hzW ⟨g z, hKV hzK⟩ rfl).symm⟩
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact ⟨hFW ⟨k.1, hKV k.2⟩, by
        show g ((F ⟨k.1, hKV k.2⟩ : ↥D) : ℂ) ∈ K
        rw [hpt]
        exact k.2⟩
  -- `g` restricted to `W` is a homeomorphism onto `V`, so `W` is simply connected
  have hsc : SimplyConnectedSpace ↥W := by
    have he_cont : Continuous (fun z : ↥W => (⟨g z.1, (hWsub z.2).2⟩ : ↥V)) :=
      Continuous.subtype_mk hgcont _
    have he'_cont : Continuous (fun y : ↥V => (⟨((F y : ↥D) : ℂ), hFW y⟩ : ↥W)) :=
      Continuous.subtype_mk (continuous_subtype_val.comp F.continuous) _
    refine Work.BasinSC.simplyConnectedSpace_of_homeomorph
      { toEquiv :=
        { toFun := fun z => (⟨g z.1, (hWsub z.2).2⟩ : ↥V)
          invFun := fun y => (⟨((F y : ↥D) : ℂ), hFW y⟩ : ↥W)
          left_inv := ?_
          right_inv := ?_ }
        continuous_toFun := he_cont
        continuous_invFun := he'_cont }
    · intro z
      exact Subtype.ext (hkey z).symm
    · intro y
      exact Subtype.ext (hpt y)
  exact ⟨hinj, hsurj, hcompact, hsc⟩

end Work.Horn.HB

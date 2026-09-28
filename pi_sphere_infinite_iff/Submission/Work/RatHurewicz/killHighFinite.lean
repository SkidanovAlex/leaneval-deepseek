import Mathlib
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.StemsB.killToFgModel
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress

namespace Work.RatHurewicz

open scoped Topology Topology.Homotopy unitInterval



/-- **Injectivity of `πmap` through a factorisation.**  If `f.comp g = φ`, `πmap g` is onto and
`πmap φ` is injective, then `πmap f` is injective at the point `g w₀`. -/
theorem injective_piMap_of_comp_eq {W Z X : Type} [TopologicalSpace W] [TopologicalSpace Z]
    [TopologicalSpace X] (f : C(Z, X)) (g : C(W, Z)) (w₀ : W) (φ : C(W, X)) (h : f.comp g = φ)
    (hsurj : Function.Surjective (Work.StemsB.πmap g 0 w₀))
    (hinj : Function.Injective (Work.StemsB.πmap φ 0 w₀)) :
    Function.Injective (Work.StemsB.πmap f 0 (g w₀)) := by
  have hcomp : Function.Injective (Work.StemsB.πmap (f.comp g) 0 w₀) := by
    cases h
    exact hinj
  intro a b hab
  obtain ⟨a₀, rfl⟩ := hsurj a
  obtain ⟨b₀, rfl⟩ := hsurj b
  rw [← Work.StemsB.πmap_comp_apply g f 0 w₀ a₀,
    ← Work.StemsB.πmap_comp_apply g f 0 w₀ b₀] at hab
  exact congrArg (Work.StemsB.πmap g 0 w₀) (hcomp hab)


/-- **Attaching `(n+2)`-cells is onto on `π_{k+1}` for `k ≤ n`.**

The pair `(attachCells n Y ι f, range (attachIncl n Y ι f))` is `(n+1)`-connected
(`Work.RatHurewicz.compressRel_attachCells_range`), so every map of pairs
`(I^{k+1}, ∂I^{k+1}) → (Y', range attachIncl)` with `k + 1 ≤ n + 1` is homotopic, relative to the
boundary, into the range; such a map therefore lifts back to `Y` through the homeomorphism
`Work.RatHurewicz.rangeHomeo` of the range with `Y`.  This is the general form of
`Work.RatHurewicz.surjective_πmap_attachIncl` (the case `k = n`, i.e. the *bottom* degree of the
pair sequence, where the attachment kills `π_{n+1}`); here `k` may be any index `≤ n`, which is
what makes the tower below able to keep all the groups `π_j` with `j ≤ n` trivial. -/
theorem surjective_piMap_attachIncl_of_le (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) (k : ℕ) (hk : k ≤ n) :
    Function.Surjective (Work.StemsB.πmap (attachIncl n Y ι f) k y₀) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have hbdr : ∀ x, x ∈ Cube.boundary (Fin (k + 1)) →
        p x ∈ Set.range (attachIncl n Y ι f) := by
      intro x hx
      exact ⟨y₀, (p.2 x hx).symm⟩
    obtain ⟨G, hG0, hGb, hG1⟩ :=
      compressRel_attachCells_range n Y ι f (k + 1) (by omega) p.1 hbdr
    have hc : Continuous fun x : ICube (k + 1) =>
        (⟨G (x, 1), hG1 x⟩ : ↥(Set.range (attachIncl n Y ι f))) :=
      Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const))
        (fun x => hG1 x)
    have hbd : ∀ y ∈ Cube.boundary (Fin (k + 1)),
        (rangeHomeo n Y ι f).symm ⟨G (y, 1), hG1 y⟩ = y₀ := by
      intro y hy
      have hGy : G (y, 1) = attachIncl n Y ι f y₀ := by
        rw [hGb y hy 1, p.2 y hy]
      have hsub : (⟨G (y, 1), hG1 y⟩ : ↥(Set.range (attachIncl n Y ι f))) =
          ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ := by
        refine Subtype.ext ?_
        exact hGy
      rw [hsub]
      exact rangeHomeo_symm_basepoint n Y ι f y₀
    let g : Ω^ (Fin (k + 1)) Y y₀ :=
      ⟨⟨fun x => (rangeHomeo n Y ι f).symm ⟨G (x, 1), hG1 x⟩,
          (rangeHomeo n Y ι f).symm.continuous.comp hc⟩, hbd⟩
    refine ⟨⟦g⟧, ?_⟩
    rw [Work.StemsB.πmap_apply_mk]
    have hhom : GenLoop.Homotopic p (Work.StemsB.genLoopMap (attachIncl n Y ι f) (k + 1) g) := by
      refine ⟨⟨⟨fun w : I × ICube (k + 1) => G (w.2, w.1),
        G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩, ?_, ?_⟩, ?_⟩
      · intro x
        exact hG0 x
      · intro x
        show G (x, 1) = attachIncl n Y ι f (g x)
        exact (rangeHomeo_symm_apply_attachIncl n Y ι f ⟨G (x, 1), hG1 x⟩).symm
      · intro t x hx
        exact hGb x hx t
    exact (Quotient.sound hhom).symm

/-- **The killing tower, preserving `π₀` and `π₁`.** -/

theorem killTowerAux (n : ℕ) :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (X : Type) [TopologicalSpace X] (Y : Type) [TopologicalSpace Y] (y₀ : Y) (φ : C(Y, X)),
      (∀ x : X, Subsingleton (HomotopyGroup (Fin 0) X x)) →
      (∀ i : ℕ, k + 1 ≤ i → i ≤ k + n → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x)) →
      Subsingleton (HomotopyGroup (Fin 0) Y y₀) →
      Finite (HomotopyGroup (Fin 1) Y y₀) →
      Function.Injective (Work.StemsB.πmap φ 0 y₀) →
      (∀ j : ℕ, 2 ≤ j → j ≤ k → Subsingleton (HomotopyGroup (Fin j) Y y₀)) →
      ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
        ψ.comp χ = φ ∧ Finite (HomotopyGroup (Fin 1) Y' y₀') ∧
        Function.Injective (Work.StemsB.πmap ψ 0 y₀') ∧
        Subsingleton (HomotopyGroup (Fin 0) Y' y₀') ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ k + n → Subsingleton (HomotopyGroup (Fin j) Y' y₀')) := by
  induction n with
  | zero =>
    intro k hk X _ Y _ y₀ φ hX0 hX hY0 hfin hinj hlo
    exact ⟨Y, inferInstance, y₀, φ, ContinuousMap.id Y, by ext y; rfl, hfin, hinj, hY0,
      fun j hj2 hj => hlo j hj2 (by omega)⟩
  | succ m ih =>
    intro k hk X _ Y _ y₀ φ hX0 hX hY0 hfin hinj hlo
    let ι := HomotopyGroup (Fin (k + 1)) Y y₀
    let f : ι → C(cellSphere k, Y) := killFamily k Y y₀
    let Y₁ : Type := attachCells k Y ι f
    letI : TopologicalSpace Y₁ := inferInstance
    let χ₁ : C(Y, Y₁) := attachIncl k Y ι f
    let y₁ : Y₁ := χ₁ y₀
    have hXstep : Subsingleton (HomotopyGroup (Fin (k + 1)) X (φ y₀)) :=
      hX (k + 1) le_rfl (by omega) (φ y₀)
    obtain ⟨ψ₁, hψ₁⟩ := Work.StemsB.killFamily_extend k Y y₀ X φ hXstep
    have hsurj₁ : Function.Surjective (Work.StemsB.πmap χ₁ 0 y₀) :=
      surjective_piMap_attachIncl_of_le k Y ι f y₀ 0 (by omega)
    have hY₁0 : Subsingleton (HomotopyGroup (Fin 0) Y₁ y₁) :=
      Work.StemsB.subsingleton_of_surjective (HomotopyGroup.map (N := Fin 0) χ₁)
        (Work.Serre.attachIncl_pi0_bijective k Y ι f y₀).2 hY0
    haveI := hfin
    have hfin₁ : Finite (HomotopyGroup (Fin 1) Y₁ y₁) :=
      Finite.of_surjective (Work.StemsB.πmap χ₁ 0 y₀) hsurj₁
    have hinj₁ : Function.Injective (Work.StemsB.πmap ψ₁ 0 y₁) :=
      injective_piMap_of_comp_eq ψ₁ χ₁ y₀ φ hψ₁ hsurj₁ hinj
    have hlo₁ : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → Subsingleton (HomotopyGroup (Fin j) Y₁ y₁) := by
      intro j hj2 hjk1
      rcases eq_or_lt_of_le hjk1 with heq | hlt
      · subst heq
        exact killFamily_subsingleton k Y y₀
      · have hjk : j ≤ k := by omega
        have hb := surjective_piMap_attachIncl_of_le k Y ι f y₀ (j - 1) (by omega)
        have hsi : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
        have h1 : Subsingleton (HomotopyGroup (Fin (j - 1 + 1)) Y y₀) := by
          simpa only [hsi] using hlo j hj2 hjk
        simpa only [hsi] using Work.StemsB.subsingleton_of_surjective (Work.StemsB.πmap χ₁ (j - 1) y₀) hb h1
    have hX' : ∀ i : ℕ, (k + 1) + 1 ≤ i → i ≤ (k + 1) + m →
        ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x) :=
      fun i hi hle => hX i (by omega) (by omega)
    obtain ⟨Y', instY', y₀', ψ', χ', hχ', hfin', hinj', hY₀', hkilled'⟩ :=
      ih (k + 1) (by omega) X Y₁ y₁ ψ₁ hX0 hX' hY₁0 hfin₁ hinj₁ hlo₁
    refine ⟨Y', instY', y₀', ψ', χ'.comp χ₁, ?_, hfin', hinj', hY₀', ?_⟩
    · rw [← ContinuousMap.comp_assoc, hχ', hψ₁]
    · intro j hj2 hle
      exact hkilled' j hj2 (by omega)

/-- **Killing `π_i` for `2 ≤ i ≤ N` preserves `π₁`.**

If `X`, `Y` are path connected, `φ : Y → X` is a based map with `π₁(Y)` finite and `π₁(Y) → π₁(X)`
injective, and `π_i(X, φ y₀)` is trivial for `2 ≤ i ≤ N`, then there is a space `Y'` (path
connected) with a map `ψ : Y' → X`, a map `χ : Y → Y'` with `ψ ∘ χ = φ`, such that `π₁(Y')` is
finite, `π₁(Y') → π₁(X)` is injective, and `π_i(Y')` is trivial for `2 ≤ i ≤ N`.

Intended route: the classical killing tower — for `i = 2, …, N` successively attach, for each
element of `π_i` of the current stage, an `(i+1)`-cell along a representative sphere map
(`Work.RatHurewicz.attachCells (i-1)` with the family `Work.RatHurewicz.killFamily (i-1)`), and
extend the map to `X` at each step because `π_i(X) = 0` (`Work.StemsB.killFamily_extend`; the
pattern is `Work.StemsB.killToFgModel`'s `killTower`, whose induction is directly reusable with
`k := 2`).  Attaching cells of dimension `≥ 3` does not change `π₁` or `π₀`
(`Work.Serre.attachIncl_piMap_bijective_of_compress` at `i = 1`, `0`), and each step kills the
corresponding `π_i` (`Work.RatHurewicz.killFamily_subsingleton`); the later steps do not recreate
the earlier `π_i`, so the final space has `π_i = 0` for `2 ≤ i ≤ N`. -/
theorem killHighFinite (X : Type) [TopologicalSpace X] (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (φ : C(Y, X)) (N : ℕ)
    (hX0 : Subsingleton (HomotopyGroup (Fin 0) X (φ y₀)))
    (hX : ∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) X (φ y₀)))
    (hY0 : Subsingleton (HomotopyGroup (Fin 0) Y y₀))
    (hfin : Finite (HomotopyGroup (Fin 1) Y y₀))
    (hinj : Function.Injective (Work.StemsB.πmap φ 0 y₀)) :
    ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
      ψ.comp χ = φ ∧ Finite (HomotopyGroup (Fin 1) Y' y₀') ∧
      Function.Injective (Work.StemsB.πmap ψ 0 y₀') ∧
      Subsingleton (HomotopyGroup (Fin 0) Y' y₀') ∧
      (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) Y' y₀')) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · exact ⟨Y, inferInstance, y₀, φ, ContinuousMap.id Y, by ext y; rfl, hfin, hinj, hY0,
      fun i hi2 hiN => absurd hi2 (by omega)⟩
  · haveI := hX0
    have hZ : Subsingleton (ZerothHomotopy X) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := φ y₀)).surjective.subsingleton
    haveI : PathConnectedSpace X :=
      pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk (φ y₀)⟩, hZ⟩
    have hX0all : ∀ x : X, Subsingleton (HomotopyGroup (Fin 0) X x) := fun x =>
      (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).subsingleton
    have hXall : ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ x : X,
        Subsingleton (HomotopyGroup (Fin i) X x) := by
      intro i hi2 hiN x
      have hsi : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      have h1 : Subsingleton (HomotopyGroup (Fin (i - 1 + 1)) X (φ y₀)) := by
        simpa only [hsi] using hX i hi2 hiN
      simpa only [hsi] using Work.Serre.subsingleton_homotopyGroup_of_joined
        (PathConnectedSpace.joined (φ y₀) x) (i - 1) h1
    obtain ⟨Y', instY', y₀', ψ, χ, hχ, hfin', hinj', hY₀', hkilled⟩ :=
      killTowerAux (N - 1) 1 (by omega) X Y y₀ φ hX0all
        (fun i hi hle => hXall i (by omega) (by omega)) hY0 hfin hinj
        (fun j hj2 hj1 => absurd hj2 (by omega))
    exact ⟨Y', instY', y₀', ψ, χ, hχ, hfin', hinj', hY₀',
      fun i hi2 hiN => hkilled i hi2 (by omega)⟩


end Work.RatHurewicz

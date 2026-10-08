import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Transport of the full Singer-cycle package along a group isomorphism

Given a group isomorphism `e : X ≃* Y` and a subgroup `V ≤ X` together with the data

* `V` cyclic of order `c` (`hcyc`, `hcard`),
* `C_X(V) = V` (`hcent`),
* `|N_X(V)| = c'` (`hnorm`),
* an involution `τ ∈ X` inverting `V` (`hτ`),

the image `W = e(V) ≤ Y` satisfies all of the same properties, and in addition every element
of `W` is *strongly real*, i.e. a product of two involutions.

The last point is not an extra hypothesis on `V`: if `τ` inverts `V` and `τ² = 1`, then for every
`w ∈ V` the element `τ w` is an involution (`(τ w)² = τ w τ w = w⁻¹ w = 1`) and
`(τ w) · τ = w⁻¹`, so `w⁻¹` and hence `w` is a product of two involutions.
-/

namespace Work.ZassenhausSuzuki.SingerModelCycle

theorem transport_singer {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (V : Subgroup X)
    (c c' : ℕ) (hcyc : IsCyclic ↥V) (hcard : Nat.card ↥V = c)
    (hcent : Subgroup.centralizer (V : Set X) = V)
    (hnorm : Nat.card ↥(Subgroup.normalizer (V : Set X)) = c')
    (hτ : ∃ τ : X, τ * τ = 1 ∧ ∀ v ∈ V, τ * v * τ⁻¹ = v⁻¹) :
    ∃ W : Subgroup Y, IsCyclic ↥W ∧ Nat.card ↥W = c ∧
      Subgroup.centralizer (W : Set Y) = W ∧
      Nat.card ↥(Subgroup.normalizer (W : Set Y)) = c' ∧
      (∃ τ : Y, τ * τ = 1 ∧ ∀ v ∈ W, τ * v * τ⁻¹ = v⁻¹) ∧
      (∀ s ∈ W, ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = s) := by
  classical
  -- `W` is the image of `V` under `e`.
  let W : Subgroup Y := V.map (e : X →* Y)
  have hmem : ∀ y : Y, y ∈ W ↔ e.symm y ∈ V := fun y => Subgroup.mem_map_equiv
  -- ## Cyclicity
  have hcyc' : IsCyclic ↥W := by
    refine isCyclic_of_surjective (hH := hcyc)
      ({ toFun := fun v => (⟨e (v : X), by
            rw [hmem (e (v : X)), e.symm_apply_apply]; exact v.2⟩ : ↥W)
         map_one' := by ext; simp
         map_mul' := fun a b => by ext; simp } : ↥V →* ↥W) ?_
    intro y
    exact ⟨⟨e.symm (y : Y), (hmem (y : Y)).mp y.2⟩, by ext; simp⟩
  -- ## Cardinality
  have hcard' : Nat.card ↥W = Nat.card ↥V :=
    (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv
      (fun x => ((hmem (e x)).trans (by rw [e.symm_apply_apply])).symm))).symm
  -- ## Self-centralising
  have hcent' : Subgroup.centralizer (W : Set Y) = W := by
    refine le_antisymm ?_ ?_
    · intro y hy
      rw [hmem (y : Y)]
      rw [← hcent, Subgroup.mem_centralizer_iff]
      rw [Subgroup.mem_centralizer_iff] at hy
      intro v hv
      have hvW : e v ∈ W := (hmem (e v)).mpr (by rw [e.symm_apply_apply]; exact hv)
      have h2 : e v * y = y * e v := hy (e v) hvW
      have h3 := congrArg e.symm h2
      simpa using h3
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hy' : e.symm y ∈ V := (hmem (y : Y)).mp hy
      have hw' : e.symm w ∈ V := (hmem (w : Y)).mp hw
      have h2 : e.symm w * e.symm y = e.symm y * e.symm w :=
        (Subgroup.mem_centralizer_iff.mp (by rw [hcent]; exact hy')) (e.symm w) hw'
      have h3 := congrArg e h2
      simpa using h3
  -- ## Normaliser cardinality
  have hnorm' : Nat.card ↥(Subgroup.normalizer (W : Set Y)) =
      Nat.card ↥(Subgroup.normalizer (V : Set X)) := by
    have hmap : Subgroup.normalizer (W : Set Y)
        = (Subgroup.normalizer (V : Set X)).map (e : X →* Y) :=
      (Subgroup.map_equiv_normalizer_eq V e).symm
    rw [hmap]
    exact (Nat.card_congr
      ((Subgroup.normalizer (V : Set X)).equivMapOfInjective (e : X →* Y) e.injective).toEquiv).symm
  -- ## The inverting involution
  obtain ⟨τ, hτ2, hτinv⟩ := hτ
  have hinv' : ∃ τ' : Y, τ' * τ' = 1 ∧ ∀ v ∈ W, τ' * v * τ'⁻¹ = v⁻¹ := by
    refine ⟨e τ, ?_, ?_⟩
    · rw [← map_mul, hτ2, map_one]
    · intro w hw
      rw [hmem (w : Y)] at hw
      apply e.symm.injective
      simpa using hτinv (e.symm w) hw
  -- ## Strong reality of the elements of `W`
  have hsr' : ∀ s ∈ W, ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = s := by
    intro s hs
    obtain ⟨τY, hτY2, hτYinv⟩ := hinv'
    have hτYinv' : τY⁻¹ = τY := inv_eq_of_mul_eq_one_right hτY2
    have hs'inv : s⁻¹ ∈ W := W.inv_mem hs
    have h1 : τY * s⁻¹ * τY⁻¹ = s := by
      have h := hτYinv s⁻¹ hs'inv
      rwa [inv_inv] at h
    have key1 : τY * s⁻¹ * τY = s := by rwa [hτYinv'] at h1
    have key2 : (τY * s⁻¹) * (τY * s⁻¹) = 1 := by
      rw [show (τY * s⁻¹) * (τY * s⁻¹) = ((τY * s⁻¹) * τY) * s⁻¹ by
            simp only [mul_assoc],
        key1, mul_inv_cancel]
    exact ⟨τY * s⁻¹, τY, key2, hτY2, key1⟩
  exact ⟨W, hcyc', hcard'.trans hcard, hcent', hnorm'.trans hnorm, hinv', hsr'⟩

end Work.ZassenhausSuzuki.SingerModelCycle

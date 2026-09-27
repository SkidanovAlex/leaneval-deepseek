import Mathlib

/-!
# An `n`-plane in `ℝ^{2n}` transverse to two given `n`-planes

`Work.Drive.Push.planeTransverse`: given two `n`-dimensional subspaces `V`, `W` of `ℝ^{2n}`
there is an `n`-dimensional subspace `H` with `H ⊓ V = ⊥` and `H ⊓ W = ⊥`.

The construction is explicit.  Put `D = V ⊓ W`, choose a complement `C` of `D`, set
`A = V ⊓ C`, `B = W ⊓ C` (so `V = D ⊔ A`, `W = D ⊔ B`, and `A ⊓ B = ⊥`, `finrank A = finrank B`),
and let `G ≤ A ⊔ B` be the graph of a linear isomorphism `A ≃ B` (`exists_transverse`).  Finally
let `Z` be a complement of `D ⊔ A ⊔ B`.  Then `H := G ⊔ Z` has `finrank H = finrank V` and is
transverse to both `V` and `W`: a vector of `H ⊓ V` decomposes as `g + z` with `g ∈ G ≤ A ⊔ B`,
so `z ∈ D ⊔ A ⊔ B` while `z ∈ Z`, hence `z = 0`, and then `g ∈ V` forces `g = 0` by the graph
property.
-/

namespace Work.Drive.Push

open Module Submodule

/-- The dimension of a sum of two submodules is the sum of the dimensions when they meet in `⊥`. -/
private lemma finrank_sup_of_disjoint_pair {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] {p q : Submodule ℝ X} (h : p ⊓ q = ⊥) :
    Module.finrank ℝ ↥(p ⊔ q) = Module.finrank ℝ ↥p + Module.finrank ℝ ↥q := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq p q
  rw [h, finrank_bot, add_zero] at h1
  exact h1

/-- **The graph of an isomorphism**: if `A`, `B` are submodules with `A ⊓ B = ⊥` and equal
dimension, there is a submodule `L ≤ A ⊔ B` of dimension `finrank A` that is transverse to both
`V` and `W`, whenever `A ≤ V`, `B ≤ W`, `A, B ≤ C` and `C ⊓ V ⊓ W = ⊥`. -/
private lemma exists_transverse {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] {A B V W C : Submodule ℝ X} (hA : A ≤ V) (hB : B ≤ W) (hAC : A ≤ C)
    (hBC : B ≤ C) (hC : (V ⊓ W) ⊓ C = ⊥) (hAB : A ⊓ B = ⊥)
    (hdim : Module.finrank ℝ ↥A = Module.finrank ℝ ↥B) :
    ∃ L : Submodule ℝ X, L ⊓ V = ⊥ ∧ L ⊓ W = ⊥ ∧ L ≤ A ⊔ B ∧
      Module.finrank ℝ ↥L = Module.finrank ℝ ↥A := by
  classical
  let ψ : A ≃ₗ[ℝ] B := LinearEquiv.ofFinrankEq A B hdim
  let g : A →ₗ[ℝ] X := A.subtype + B.subtype.comp ψ.toLinearMap
  have hg : ∀ a : A, g a = (↑a : X) + ↑(ψ a) := by intro a; rfl
  refine ⟨LinearMap.range g, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxL, hxV⟩
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hxL
    have hψV : (↑(ψ a) : X) ∈ V := by
      have h : g a - ↑a ∈ V := Submodule.sub_mem _ hxV (hA a.2)
      rwa [hg a, add_sub_cancel_left] at h
    have h1 : (↑(ψ a) : X) ∈ (V ⊓ W) ⊓ C :=
      Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hψV, hB (ψ a).2⟩, hBC (ψ a).2⟩
    rw [hC] at h1
    have hψ0 : ψ a = 0 := Subtype.ext (by simpa using h1)
    have ha0 : a = 0 := ψ.injective (by rw [hψ0, map_zero])
    rw [hg a, ha0, map_zero]
    simp
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxL, hxW⟩
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hxL
    have haW : (↑a : X) ∈ W := by
      have h : g a - ↑(ψ a) ∈ W := Submodule.sub_mem _ hxW (hB (ψ a).2)
      rwa [hg a, add_sub_cancel_right] at h
    have h1 : (↑a : X) ∈ (V ⊓ W) ⊓ C :=
      Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hA a.2, haW⟩, hAC a.2⟩
    rw [hC] at h1
    have ha0 : a = 0 := Subtype.ext (by simpa using h1)
    rw [hg a, ha0, map_zero]
    simp
  · rintro x ⟨a, rfl⟩
    rw [Submodule.mem_sup]
    exact ⟨↑a, a.2, ↑(ψ a), (ψ a).2, (hg a).symm⟩
  · have hker : LinearMap.ker g = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro a ha
      rw [LinearMap.mem_ker] at ha
      have h : (↑a : X) + ↑(ψ a) = 0 := by rwa [hg a] at ha
      have hψA : (↑(ψ a) : X) ∈ A := by
        have h1 : (↑(ψ a) : X) = -↑a := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h
        rw [h1]
        exact neg_mem a.2
      have h1 : (↑(ψ a) : X) ∈ A ⊓ B := Submodule.mem_inf.mpr ⟨hψA, (ψ a).2⟩
      rw [hAB] at h1
      have hψ0 : ψ a = 0 := Subtype.ext (by simpa using h1)
      exact ψ.injective (by rw [hψ0, map_zero])
    have h2 := LinearMap.finrank_range_add_finrank_ker g
    rw [hker, finrank_bot, add_zero] at h2
    exact h2

/-- In a space of dimension `finrank V + finrank W` there is a common complement of two
submodules `V`, `W` of equal dimension. -/
private lemma exists_common_complement {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] (V W : Submodule ℝ X)
    (hVW : Module.finrank ℝ ↥V = Module.finrank ℝ ↥W)
    (hX : Module.finrank ℝ X = Module.finrank ℝ ↥V + Module.finrank ℝ ↥W) :
    ∃ H : Submodule ℝ X, Module.finrank ℝ ↥H = Module.finrank ℝ ↥V ∧ H ⊓ V = ⊥ ∧
      H ⊓ W = ⊥ := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (V ⊓ W)
  have hDC : (V ⊓ W) ⊓ C = ⊥ := hC.inf_eq_bot
  have hCDtop : (V ⊓ W) ⊔ C = ⊤ := hC.sup_eq_top
  -- the two splittings `V = (V ⊓ W) ⊔ (V ⊓ C)`, `W = (V ⊓ W) ⊔ (W ⊓ C)`
  have hVsplit : (V ⊓ W) ⊔ (V ⊓ C) = V := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    intro v hv
    have hvtop : v ∈ (V ⊓ W) ⊔ C := by rw [hCDtop]; exact Submodule.mem_top
    obtain ⟨d, hd, c, hc, hdc⟩ := Submodule.mem_sup.mp hvtop
    have hcV : c ∈ V := by
      have h : c = v - d := by rw [← hdc, add_sub_cancel_left]
      rw [h]
      exact Submodule.sub_mem _ hv hd.1
    exact Submodule.mem_sup.mpr ⟨d, hd, c, Submodule.mem_inf.mpr ⟨hcV, hc⟩, hdc⟩
  have hWsplit : (V ⊓ W) ⊔ (W ⊓ C) = W := by
    refine le_antisymm (sup_le inf_le_right inf_le_left) ?_
    intro v hv
    have hvtop : v ∈ (V ⊓ W) ⊔ C := by rw [hCDtop]; exact Submodule.mem_top
    obtain ⟨d, hd, c, hc, hdc⟩ := Submodule.mem_sup.mp hvtop
    have hcW : c ∈ W := by
      have h : c = v - d := by rw [← hdc, add_sub_cancel_left]
      rw [h]
      exact Submodule.sub_mem _ hv hd.2
    exact Submodule.mem_sup.mpr ⟨d, hd, c, Submodule.mem_inf.mpr ⟨hcW, hc⟩, hdc⟩
  -- the three pairwise intersections
  have hdisjV : (V ⊓ W) ⊓ (V ⊓ C) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_inf] at hx
    obtain ⟨⟨hxV, hxW⟩, _, hxC⟩ := hx
    have hx' : x ∈ (V ⊓ W) ⊓ C := by
      simp only [Submodule.mem_inf]; exact ⟨⟨hxV, hxW⟩, hxC⟩
    rw [hDC] at hx'
    simpa using hx'
  have hdisjW : (V ⊓ W) ⊓ (W ⊓ C) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_inf] at hx
    obtain ⟨⟨hxV, hxW⟩, _, hxC⟩ := hx
    have hx' : x ∈ (V ⊓ W) ⊓ C := by
      simp only [Submodule.mem_inf]; exact ⟨⟨hxV, hxW⟩, hxC⟩
    rw [hDC] at hx'
    simpa using hx'
  have hV'W' : (V ⊓ C) ⊓ (W ⊓ C) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_inf] at hx
    obtain ⟨⟨hxV, hxC⟩, hxW, _⟩ := hx
    have hx' : x ∈ (V ⊓ W) ⊓ C := by
      simp only [Submodule.mem_inf]; exact ⟨⟨hxV, hxW⟩, hxC⟩
    rw [hDC] at hx'
    simpa using hx'
  -- dimensions
  have hdimV : Module.finrank ℝ ↥V =
      Module.finrank ℝ ↥(V ⊓ W) + Module.finrank ℝ ↥(V ⊓ C) := by
    conv_lhs => rw [← hVsplit]
    exact finrank_sup_of_disjoint_pair hdisjV
  have hdimW : Module.finrank ℝ ↥W =
      Module.finrank ℝ ↥(V ⊓ W) + Module.finrank ℝ ↥(W ⊓ C) := by
    conv_lhs => rw [← hWsplit]
    exact finrank_sup_of_disjoint_pair hdisjW
  have hdim : Module.finrank ℝ ↥(V ⊓ C) = Module.finrank ℝ ↥(W ⊓ C) := by omega
  -- the graph
  obtain ⟨L, hLV, hLW, hLs, hLdim⟩ :=
    exists_transverse (A := V ⊓ C) (B := W ⊓ C) inf_le_left inf_le_left inf_le_right inf_le_right
      hDC hV'W' hdim
  -- a complement of `D ⊔ A ⊔ B`
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl ((V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C)))
  have hVT : V ≤ (V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C)) := by
    conv_lhs => rw [← hVsplit]
    exact sup_le le_sup_left (le_trans le_sup_left le_sup_right)
  have hWT : W ≤ (V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C)) := by
    conv_lhs => rw [← hWsplit]
    exact sup_le le_sup_left (le_trans le_sup_right le_sup_right)
  have hLZ : L ⊓ Z = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxL, hxZ⟩
    have hxT : x ∈ (V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C)) := le_trans hLs le_sup_right hxL
    have hx1 : x ∈ ((V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C))) ⊓ Z :=
      Submodule.mem_inf.mpr ⟨hxT, hxZ⟩
    rw [hZ.inf_eq_bot] at hx1
    simpa using hx1
  -- dimension bookkeeping
  have hdimH : Module.finrank ℝ ↥(L ⊔ Z) = Module.finrank ℝ ↥L + Module.finrank ℝ ↥Z :=
    finrank_sup_of_disjoint_pair hLZ
  have hdimXZ : Module.finrank ℝ X =
      Module.finrank ℝ ↥((V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C))) + Module.finrank ℝ ↥Z := by
    have h := finrank_sup_of_disjoint_pair hZ.inf_eq_bot
    rw [hZ.sup_eq_top, finrank_top] at h
    exact h
  have hdimT : Module.finrank ℝ ↥((V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C))) =
      Module.finrank ℝ ↥(V ⊓ W) + Module.finrank ℝ ↥((V ⊓ C) ⊔ (W ⊓ C)) := by
    apply finrank_sup_of_disjoint_pair
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxD, hxS⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxS
    have hxC : x ∈ C := by
      rw [← hab]
      exact Submodule.add_mem C ha.2 hb.2
    have hx1 : x ∈ (V ⊓ W) ⊓ C := Submodule.mem_inf.mpr ⟨hxD, hxC⟩
    rw [hDC] at hx1
    simpa using hx1
  have hdimS : Module.finrank ℝ ↥((V ⊓ C) ⊔ (W ⊓ C)) =
      Module.finrank ℝ ↥(V ⊓ C) + Module.finrank ℝ ↥(W ⊓ C) :=
    finrank_sup_of_disjoint_pair hV'W'
  refine ⟨L ⊔ Z, ?_, ?_, ?_⟩
  · omega
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxH, hxV⟩
    obtain ⟨l, hl, z, hz, hlz⟩ := Submodule.mem_sup.mp hxH
    have hz0 : z = 0 := by
      have hzl : z = x - l := by rw [← hlz, add_sub_cancel_left]
      have hx1 : z ∈ ((V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C))) ⊓ Z :=
        Submodule.mem_inf.mpr ⟨by
          rw [hzl]
          exact Submodule.sub_mem _ (hVT hxV) (le_trans hLs le_sup_right hl), hz⟩
      rw [hZ.inf_eq_bot] at hx1
      simpa using hx1
    have hlV : l ∈ V := by
      have hh := hxV
      rw [← hlz, hz0, add_zero] at hh
      exact hh
    have hx1 : l ∈ L ⊓ V := Submodule.mem_inf.mpr ⟨hl, hlV⟩
    rw [hLV] at hx1
    rw [← hlz, hz0, add_zero]
    simpa using hx1
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxH, hxW⟩
    obtain ⟨l, hl, z, hz, hlz⟩ := Submodule.mem_sup.mp hxH
    have hz0 : z = 0 := by
      have hzl : z = x - l := by rw [← hlz, add_sub_cancel_left]
      have hx1 : z ∈ ((V ⊓ W) ⊔ ((V ⊓ C) ⊔ (W ⊓ C))) ⊓ Z :=
        Submodule.mem_inf.mpr ⟨by
          rw [hzl]
          exact Submodule.sub_mem _ (hWT hxW) (le_trans hLs le_sup_right hl), hz⟩
      rw [hZ.inf_eq_bot] at hx1
      simpa using hx1
    have hlW : l ∈ W := by
      have hh := hxW
      rw [← hlz, hz0, add_zero] at hh
      exact hh
    have hx1 : l ∈ L ⊓ W := Submodule.mem_inf.mpr ⟨hl, hlW⟩
    rw [hLW] at hx1
    rw [← hlz, hz0, add_zero]
    simpa using hx1

theorem planeTransverse {n : ℕ}
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
    (hV : Module.finrank ℝ V = n) (hW : Module.finrank ℝ W = n) :
    ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))),
      Module.finrank ℝ H = n ∧ H ⊓ V = ⊥ ∧ H ⊓ W = ⊥ := by
  obtain ⟨H, hHdim, hHV, hHW⟩ :=
    exists_common_complement (X := EuclideanSpace ℝ (Fin (2 * n))) V W
      (by rw [hV, hW])
      (by rw [finrank_euclideanSpace_fin, hV, hW]; omega)
  exact ⟨H, by rw [hHdim, hV], hHV, hHW⟩

end Work.Drive.Push

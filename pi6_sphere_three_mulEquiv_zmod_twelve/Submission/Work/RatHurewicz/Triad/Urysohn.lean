import Mathlib
import Submission.Work.RatHurewicz.Triad.Basic
import Submission.Work.RatHurewicz.Triad.Helpers

/-!
# The dimension count and the Urysohn step (tom Dieck 6.9.3)

Given a map `Ψ : I^{n+1} → X` which is admissible for the triad `(X; B, C)` and which satisfies the
`K`/`G` conditions of the preparation theorem for the mesh `1/N` (in the pointwise form of
`Work.RatHurewicz.Triad.IsSmall`/`IsLarge`), and given `n ≤ p + q + 1`, this file deforms `Ψ`,
through admissible maps, into a map with image in `B`.

The two closed sets that have to be separated are

* `A = π(Ψ⁻¹(X ∖ B))` — where the map is "bad for `B`", and
* `∂Iⁿ ∪ π(Ψ⁻¹(X ∖ C))` — where it must not be moved,

`π = initC n` being the projection onto the space coordinates.  Their disjointness is the
dimension count: a point of `π(Ψ⁻¹(X∖C))` has at least `p+1` coordinates in the *lower* half of
their grid interval, a point of `π(Ψ⁻¹(X∖B))` has at least `q+1` in the *upper* half, the two
conditions exclude each other coordinatewise, and `n ≤ p + q + 1`.  Since `I^{n+1}` is compact and
`B` is open, `A` is closed.  An Urysohn function `φ : Iⁿ → I` with `φ = 0` on `A` and `φ = 1` on
`∂Iⁿ ∪ π(Ψ⁻¹(X∖C))` then reparametrises the time of the paths.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.Stems.Cubical

/-- `initC` is continuous. -/
theorem continuous_initC (n : ℕ) : Continuous fun z : ICube (n + 1) => initC n z :=
  continuous_pi fun i => continuous_apply i.castSucc

/-- The boundary of the cube is closed. -/
theorem isClosed_boundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have h : Cube.boundary (Fin n) =
      ⋃ i : Fin n, ({x : ICube n | x i = 0} ∪ {x : ICube n | x i = 1}) := by
    ext x
    simp [Cube.boundary]
  rw [h]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

/-- **The dimension count of tom Dieck (6.9.3).**  The two sets that the Urysohn function has to
separate are disjoint. -/
theorem count_disjoint {X : Type} [TopologicalSpace X] {B C : Set X}
    {p q n : ℕ} (hn : n ≤ p + q + 1) {N : ℕ}
    (Ψ : C(ICube (n + 1), X))
    (hΨbd : ∀ x : ICube n, x ∈ Cube.boundary (Fin n) → ∀ t : I, Ψ (Fin.snoc x t) ∈ B)
    (hK : ∀ z : ICube (n + 1), Ψ z ∉ C →
      ∃ L : Finset (Fin n), p + 1 ≤ L.card ∧ ∀ i ∈ L, IsSmall N z i.castSucc)
    (hG : ∀ z : ICube (n + 1), Ψ z ∉ B →
      ∃ L : Finset (Fin n), q + 1 ≤ L.card ∧ ∀ i ∈ L, IsLarge N z i.castSucc) :
    Disjoint {y : ICube n | ∃ z : ICube (n + 1), initC n z = y ∧ Ψ z ∉ B}
      (Cube.boundary (Fin n) ∪
        {y : ICube n | ∃ z : ICube (n + 1), initC n z = y ∧ Ψ z ∉ C}) := by
  rw [Set.disjoint_left]
  rintro y ⟨z₁, hz₁, hB₁⟩ (hy | ⟨z₂, hz₂, hC₂⟩)
  · have h1 : z₁ = Fin.snoc y (z₁ (Fin.last n)) := by
      rw [← hz₁, snoc_initC]
    have h2 : Ψ z₁ ∈ B := by
      rw [h1]
      exact hΨbd y hy (z₁ (Fin.last n))
    exact hB₁ h2
  · obtain ⟨L₁, hcard₁, hL₁⟩ := hG z₁ hB₁
    obtain ⟨L₂, hcard₂, hL₂⟩ := hK z₂ hC₂
    have hdisj : Disjoint L₁ L₂ := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      have hcoord : (z₁ a.castSucc : ℝ) = (z₂ a.castSucc : ℝ) := by
        have h1 : initC n z₁ a = initC n z₂ a := by rw [hz₁, hz₂]
        exact congrArg Subtype.val h1
      refine not_isSmall_of_isLarge ?_ (hL₂ a hb)
      unfold IsLarge at hL₁ ⊢
      rw [← hcoord]
      exact hL₁ a ha
    have hcard : L₁.card + L₂.card ≤ n := by
      have h1 : L₁.card + L₂.card ≤ (Finset.univ : Finset (Fin n)).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.subset_univ _)
      simpa using h1
    omega

/-- **The Urysohn step (tom Dieck 6.9.3, second half).** -/
theorem triadUrysohn {X : Type} [TopologicalSpace X] {B C : Set X}
    (hB : IsOpen B) (hC : IsOpen C) (hBC : B ∪ C = Set.univ) (x₀ : ↥(B ∩ C)) (p q n : ℕ)
    (hn : n ≤ p + q + 1) (N : ℕ) (hN : 1 ≤ N) (Ψ : C(ICube (n + 1), X))
    (hΨ0 : ∀ x : ICube n, Ψ (Fin.snoc x 0) = (x₀ : X))
    (hΨ1 : ∀ x : ICube n, Ψ (Fin.snoc x 1) ∈ C)
    (hΨbd : ∀ x : ICube n, x ∈ Cube.boundary (Fin n) → ∀ t : I,
      Ψ (Fin.snoc x t) ∈ B)
    (hK : ∀ z : ICube (n + 1), Ψ z ∉ C →
      ∃ L : Finset (Fin n), p + 1 ≤ L.card ∧ ∀ i ∈ L, IsSmall N z i.castSucc)
    (hG : ∀ z : ICube (n + 1), Ψ z ∉ B →
      ∃ L : Finset (Fin n), q + 1 ≤ L.card ∧ ∀ i ∈ L, IsLarge N z i.castSucc) :
    ∃ Θ : C(ICube (n + 1) × I, X),
      (∀ z : ICube (n + 1), Θ (z, 0) = Ψ z) ∧
      (∀ s : I,
        (∀ x : ICube n, Θ (Fin.snoc x 0, s) = (x₀ : X)) ∧
        (∀ x : ICube n, Θ (Fin.snoc x 1, s) ∈ C) ∧
        (∀ x : ICube n, x ∈ Cube.boundary (Fin n) → ∀ t : I,
          Θ (Fin.snoc x t, s) ∈ B)) ∧
      (∀ z : ICube (n + 1), Θ (z, 1) ∈ B) := by
  set AA : Set (ICube n) :=
    {y | ∃ z : ICube (n + 1), initC n z = y ∧ Ψ z ∉ B} with hAA
  set BB : Set (ICube n) := Cube.boundary (Fin n) ∪
    {y | ∃ z : ICube (n + 1), initC n z = y ∧ Ψ z ∉ C} with hBB
  have hsb : {z : ICube (n + 1) | Ψ z ∉ B} = Ψ ⁻¹' Bᶜ := rfl
  have hsc : {z : ICube (n + 1) | Ψ z ∉ C} = Ψ ⁻¹' Cᶜ := rfl
  have hAA_cl : IsClosed AA := by
    rw [hAA]
    have hset : {y : ICube n | ∃ z : ICube (n + 1), initC n z = y ∧ Ψ z ∉ B}
        = initC n '' {z : ICube (n + 1) | Ψ z ∉ B} := by
      ext y
      constructor
      · rintro ⟨z, rfl, hz⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, rfl, hz⟩
    rw [hset]
    exact ((hB.isClosed_compl.preimage Ψ.continuous).isCompact.image
      (continuous_initC n)).isClosed
  have hBB_cl : IsClosed BB := by
    rw [hBB]
    refine (isClosed_boundary n).union ?_
    have hset : {y : ICube n | ∃ z : ICube (n + 1), initC n z = y ∧ Ψ z ∉ C}
        = initC n '' {z : ICube (n + 1) | Ψ z ∉ C} := by
      ext y
      constructor
      · rintro ⟨z, rfl, hz⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, rfl, hz⟩
    rw [hset]
    exact ((hC.isClosed_compl.preimage Ψ.continuous).isCompact.image
      (continuous_initC n)).isClosed
  have hdisj : Disjoint AA BB := by
    rw [hAA, hBB]
    exact count_disjoint hn Ψ hΨbd hK hG
  obtain ⟨f, hf0, hf1, hfr⟩ := exists_continuous_zero_one_of_isClosed hAA_cl hBB_cl hdisj
  let φ : C(ICube n, I) :=
    ⟨fun x => ⟨f x, hfr x⟩, Continuous.subtype_mk f.continuous _⟩
  have hφ0 : ∀ x ∈ AA, (φ x : ℝ) = 0 := fun x hx => by
    change f x = 0
    have h := hf0 hx
    simpa only [Pi.zero_apply] using h
  have hφ1 : ∀ x ∈ BB, (φ x : ℝ) = 1 := fun x hx => by
    change f x = 1
    have h := hf1 hx
    simpa only [Pi.one_apply] using h
  -- the modified time
  have htime : ∀ p : ICube (n + 1) × I,
      0 ≤ (p.1 (Fin.last n) : ℝ) * ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * (φ (initC n p.1) : ℝ)) ∧
      (p.1 (Fin.last n) : ℝ) * ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * (φ (initC n p.1) : ℝ)) ≤ 1 := by
    intro p
    have ht0 : (0:ℝ) ≤ (p.1 (Fin.last n) : ℝ) := (p.1 (Fin.last n)).2.1
    have ht1 : (p.1 (Fin.last n) : ℝ) ≤ 1 := (p.1 (Fin.last n)).2.2
    have hs0 : (0:ℝ) ≤ (p.2 : ℝ) := p.2.2.1
    have hs1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
    have hφ0' : (0:ℝ) ≤ (φ (initC n p.1) : ℝ) := (φ (initC n p.1)).2.1
    have hφ1' : (φ (initC n p.1) : ℝ) ≤ 1 := (φ (initC n p.1)).2.2
    have hconv0 : (0:ℝ) ≤ (1 - (p.2 : ℝ)) + (p.2 : ℝ) * (φ (initC n p.1) : ℝ) := by nlinarith
    have hconv1 : (1 - (p.2 : ℝ)) + (p.2 : ℝ) * (φ (initC n p.1) : ℝ) ≤ 1 := by nlinarith
    exact ⟨mul_nonneg ht0 hconv0, mul_le_one₀ ht1 hconv0 hconv1⟩
  let τ : ICube (n + 1) × I → I := fun p =>
    ⟨(p.1 (Fin.last n) : ℝ) * ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * (φ (initC n p.1) : ℝ)),
      (htime p).1, (htime p).2⟩
  have hτcont : Continuous τ := by
    refine Continuous.subtype_mk (Continuous.mul ?_ ?_) _
    · exact continuous_subtype_val.comp (continuous_apply (Fin.last n) |>.comp continuous_fst)
    · refine Continuous.add ?_ (Continuous.mul ?_ ?_)
      · exact continuous_const.sub (continuous_subtype_val.comp continuous_snd)
      · exact continuous_subtype_val.comp continuous_snd
      · exact (continuous_subtype_val.comp φ.continuous).comp (continuous_initC n |>.comp continuous_fst)
  have hsnocCont : Continuous fun p : ICube (n + 1) × I =>
      @Fin.snoc n (fun _ => unitInterval) (initC n p.1) (τ p) :=
    Continuous.finSnoc (A := fun _ => unitInterval)
      (f := fun p : ICube (n + 1) × I => initC n p.1) (g := τ)
      ((continuous_initC n).comp continuous_fst) hτcont
  refine ⟨⟨fun p => Ψ (@Fin.snoc n (fun _ => unitInterval) (initC n p.1) (τ p)),
    Ψ.continuous.comp hsnocCont⟩, ?_, ?_, ?_⟩
  · intro z
    change Ψ (@Fin.snoc n (fun _ => unitInterval) (initC n z) (τ (z, 0))) = Ψ z
    have h0 : τ (z, 0) = z (Fin.last n) := by
      apply Subtype.ext
      simp [τ]
    rw [h0, snoc_initC]
  · intro s
    refine ⟨?_, ?_, ?_⟩
    · intro x
      change Ψ (@Fin.snoc n (fun _ => unitInterval) (initC n (Fin.snoc x 0))
        (τ (Fin.snoc x 0, s))) = (x₀ : X)
      have h0 : τ (Fin.snoc x 0, s) = 0 := by
        apply Subtype.ext
        simp [τ]
      rw [initC_snoc, h0, hΨ0 x]
    · intro x
      change Ψ (@Fin.snoc n (fun _ => unitInterval) (initC n (Fin.snoc x 1))
        (τ (Fin.snoc x 1, s))) ∈ C
      rw [initC_snoc]
      by_cases hφ : (φ x : ℝ) = 1
      · have h1 : τ (Fin.snoc x 1, s) = 1 := by
          apply Subtype.ext
          simp only [τ]
          rw [Fin.snoc_last, initC_snoc, hφ]
          ring
        rw [h1]
        exact hΨ1 x
      · have hmem : ∀ t : I, Ψ (Fin.snoc x t) ∈ C := by
          intro t
          by_contra hc
          have hxBB : x ∈ BB := by
            rw [hBB]
            exact Or.inr ⟨Fin.snoc x t, by rw [initC_snoc], hc⟩
          exact hφ (hφ1 x hxBB)
        exact hmem _
    · intro x hx t
      change Ψ (@Fin.snoc n (fun _ => unitInterval) (initC n (Fin.snoc x t))
        (τ (Fin.snoc x t, s))) ∈ B
      rw [initC_snoc]
      have hxBB : x ∈ BB := by
        rw [hBB]; exact Or.inl hx
      have hφx : (φ x : ℝ) = 1 := hφ1 x hxBB
      have h1 : τ (Fin.snoc x t, s) = t := by
        apply Subtype.ext
        simp only [τ]
        rw [Fin.snoc_last, initC_snoc, hφx]
        ring
      rw [h1]
      exact hΨbd x hx t
  · intro z
    change Ψ (@Fin.snoc n (fun _ => unitInterval) (initC n z) (τ (z, 1))) ∈ B
    by_cases hφ : (φ (initC n z) : ℝ) = 0
    · have h1 : τ (z, 1) = 0 := by
        apply Subtype.ext
        simp only [τ]
        rw [hφ]
        simp
      rw [h1, hΨ0 (initC n z)]
      exact x₀.2.1
    · have hpos : 0 < (φ (initC n z) : ℝ) := lt_of_le_of_ne (φ _).2.1 (Ne.symm hφ)
      have hnotAA : initC n z ∉ AA := by
        intro hmem
        have := hφ0 (initC n z) hmem
        linarith
      have hmem : ∀ t : I, Ψ (Fin.snoc (initC n z) t) ∈ B := by
        intro t
        by_contra hc
        exact hnotAA ⟨Fin.snoc (initC n z) t, initC_snoc (initC n z) t, hc⟩
      exact hmem _

end

end Work.RatHurewicz.Triad

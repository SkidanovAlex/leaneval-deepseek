import Submission.Work.ThomBordism.TwoSet.Step

/-!
# The global compression over the grid

`round_aux` processes, one after another, all the cells of a finite set `T` of processable cells of
a fixed dimension, maintaining the two invariants of `Step.lean`; `advance` moves the dimension
threshold of the invariant; `process_all` runs the rounds for `Δ = 0, 1, …, j+1`; `endgame`
extracts the conclusion that the final map is `U`-valued.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {X : Type*} [TopologicalSpace X] {j N : ℕ} {U V : Set X}

/-- The processable cells of dimension `Δ`: away from the boundary and unambiguously typed. -/
noncomputable def Qall (lab : (Fin j → Fin N) → Bool) (Δ : ℕ) : Finset (CellIdx j N) := by
  classical
  exact Finset.univ.filter (fun c => Away c ∧
    ((Vcell lab c ∧ ¬ Ucell lab c) ∨ (Ucell lab c ∧ ¬ Vcell lab c)) ∧ cellDim c = Δ)

theorem mem_Qall {lab : (Fin j → Fin N) → Bool} {Δ : ℕ} {c : CellIdx j N} :
    c ∈ Qall lab Δ ↔ Away c ∧
      ((Vcell lab c ∧ ¬ Ucell lab c) ∨ (Ucell lab c ∧ ¬ Vcell lab c)) ∧ cellDim c = Δ := by
  classical
  unfold Qall
  simp

/-- The raw form in which `step` produces homotopies, as a `HomotopyRel`. -/
def homotopyRel_of_raw {f₀ f₁ : C(IC j, X)} {G : C(IC j × I, X)}
    (h0 : ∀ x, G (x, 0) = f₀ x) (h1 : ∀ x, G (x, 1) = f₁ x)
    (hbd : ∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = f₀ x) :
    f₀.HomotopyRel f₁ (Cube.boundary (Fin j)) :=
  { toHomotopy :=
      { toContinuousMap :=
          ⟨fun p : I × IC j => G (p.2, p.1),
            G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
        map_zero_left := fun x => h0 x
        map_one_left := fun x => h1 x }
    prop' := fun t x hx => hbd x hx t }

/-- **The round of a fixed dimension.**  Processing the remaining cells of `T` one after another
preserves the invariants and brings the dimension invariant to the full set `T`. -/
theorem round_aux {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hUc : ∀ d, d ≤ j → Compress ↥U {u : ↥U | (u : X) ∈ V} d)
    (Δ : ℕ) (T : Finset (CellIdx j N))
    (hT : ∀ c ∈ T, Away c ∧
      ((Vcell lab c ∧ ¬ Ucell lab c) ∨ (Ucell lab c ∧ ¬ Vcell lab c)) ∧ cellDim c = Δ) :
    ∀ Rem : Finset (CellIdx j N), Rem ⊆ T →
    ∀ g : C(IC j, X), Jinv (U := U) (V := V) lab g → Iinv (N := N) (U ∩ V) Δ (T \ Rem) g →
    ∃ (g' : C(IC j, X)) (_ : g.HomotopyRel g' (Cube.boundary (Fin j))),
      Jinv (U := U) (V := V) lab g' ∧ Iinv (N := N) (U ∩ V) Δ T g' := by
  classical
  intro Rem
  induction Rem using Finset.induction with
  | empty =>
    intro _ g hJ hI
    exact ⟨g, ContinuousMap.HomotopyRel.refl g (Cube.boundary (Fin j)), hJ, by simpa using hI⟩
  | insert a Rem' ha ih =>
    intro hRem g hJ hI
    have haT : a ∈ T := hRem (Finset.mem_insert_self a Rem')
    obtain ⟨hAway, hType, hdim⟩ := hT a haT
    obtain ⟨g₁, G, h0, h1, h2, hJ₁, hI₁⟩ := step hN hVc hUc hAway hType hdim hJ hI
    have hRel₁ : g.HomotopyRel g₁ (Cube.boundary (Fin j)) := homotopyRel_of_raw h0 h2 h1
    have hsub : Rem' ⊆ T := fun c hc => hRem (Finset.mem_insert_of_mem hc)
    have hseteq : insert a (T \ insert a Rem') = T \ Rem' := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_sdiff, not_or]
      constructor
      · rintro (rfl | ⟨hcT, hca, hcR⟩)
        · exact ⟨haT, ha⟩
        · exact ⟨hcT, hcR⟩
      · rintro ⟨hcT, hcR⟩
        by_cases hca : c = a
        · exact Or.inl hca
        · exact Or.inr ⟨hcT, hca, hcR⟩
    have hI₁' : Iinv (N := N) (U ∩ V) Δ (T \ Rem') g₁ := by
      rw [← hseteq]
      exact hI₁
    obtain ⟨g', H', hJ', hI'⟩ := ih hsub g₁ hJ₁ hI₁'
    exact ⟨g', hRel₁.trans H', hJ', hI'⟩

/-- **Advancing the dimension threshold.** -/
theorem advance {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N) {g : C(IC j, X)} {Δ : ℕ}
    {T : Finset (CellIdx j N)}
    (hT : ∀ c, Away c → ((Vcell lab c ∧ ¬ Ucell lab c) ∨ (Ucell lab c ∧ ¬ Vcell lab c)) →
      cellDim c = Δ → c ∈ T)
    (hJ : Jinv (U := U) (V := V) lab g) (hI : Iinv (N := N) (U ∩ V) Δ T g) : Iinv (N := N) (U ∩ V) (Δ + 1) ∅ g := by
  intro x hAw hd
  rcases hd with h1 | ⟨h2, h3⟩
  · by_cases hle : cellDim (cOf N x) < Δ
    · exact hI x hAw (Or.inl hle)
    · have hdim : cellDim (cOf N x) = Δ := by omega
      by_cases hamb : Vcell lab (cOf N x) ∧ Ucell lab (cOf N x)
      · exact hJ.2.2 (cOf N x) hamb.1 hamb.2 x (mem_cOf N hN x)
      · have hunamb : (Vcell lab (cOf N x) ∧ ¬ Ucell lab (cOf N x)) ∨
            (Ucell lab (cOf N x) ∧ ¬ Vcell lab (cOf N x)) := by
          rcases cell_typed hN (lab := lab) (cOf N x) with h | h
          · exact Or.inl ⟨h, fun hU => hamb ⟨h, hU⟩⟩
          · exact Or.inr ⟨h, fun hV => hamb ⟨hV, h⟩⟩
        exact hI x hAw (Or.inr ⟨hdim, hT (cOf N x) hAw hunamb hdim⟩)
  · exact absurd h3 (by simp)

/-- **All the rounds.**  After the rounds `Δ = 0, 1, …, j+1` the invariant holds with the empty
set of treated cells and the threshold `j+1`. -/
theorem process_all {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hUc : ∀ d, d ≤ j → Compress ↥U {u : ↥U | (u : X) ∈ V} d)
    (f : C(IC j, X)) (hJ : Jinv (U := U) (V := V) lab f) :
    ∀ Δ, Δ ≤ j + 1 → ∃ (g : C(IC j, X)) (_ : f.HomotopyRel g (Cube.boundary (Fin j))),
      Jinv (U := U) (V := V) lab g ∧ Iinv (N := N) (U ∩ V) Δ ∅ g := by
  intro Δ
  induction Δ with
  | zero =>
    intro _
    exact ⟨f, ContinuousMap.HomotopyRel.refl f (Cube.boundary (Fin j)), hJ,
      fun x _ hd => by
        rcases hd with h | ⟨h, hmem⟩
        · omega
        · exact absurd hmem (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro hn
    have hn' : n ≤ j + 1 := by omega
    obtain ⟨g, H, hJg, hIg⟩ := ih hn'
    obtain ⟨g', H', hJ', hI'⟩ :=
      round_aux hN hVc hUc n (Qall lab n) (fun c hc => mem_Qall.mp hc)
        (Qall lab n) (Finset.Subset.refl _) g hJg (by simpa using hIg)
    have hadv : Iinv (N := N) (U ∩ V) (n + 1) ∅ g' :=
      advance hN (fun c hAw hty hdim => mem_Qall.mpr ⟨hAw, hty, hdim⟩) hJ' hI'
    exact ⟨g', H.trans H', hJ', hadv⟩

/-- **The endgame.**  After the rounds, an unambiguous treatment or the dimension invariant brings
every value into `U`. -/
theorem endgame {lab : (Fin j → Fin N) → Bool} (hN : 1 ≤ N)
    (hfar : ∀ m, lab m = true → ∀ x ∈ boxSet m, ∀ i,
      2/(N:ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/(N:ℝ))
    {g : C(IC j, X)} (hJ : Jinv (U := U) (V := V) lab g) (hI : Iinv (N := N) (U ∩ V) (j + 1) ∅ g) :
    ∀ x, g x ∈ U := by
  intro x
  by_cases hamb : Vcell lab (cOf N x) ∧ Ucell lab (cOf N x)
  · exact (hJ.2.2 (cOf N x) hamb.1 hamb.2 x (mem_cOf N hN x)).1
  · rcases cell_typed hN (lab := lab) (cOf N x) with hV | hU
    · have hV' : Vcell lab (cOf N x) := hV
      have hAw : Away (cOf N x) := Vcell_away hN hfar hV'
      exact (hI x hAw (Or.inl (by have := cellDim_le (cOf N x); omega))).1
    · have hU' : Ucell lab (cOf N x) := hU
      exact hJ.2.1 (cOf N x) hU' (fun hV => hamb ⟨hV, hU'⟩) x (mem_cOf N hN x)

/-- **The cell-by-cell compression.** -/
theorem processCells {X : Type*} [TopologicalSpace X] {U V : Set X} {j N : ℕ} (hN : 3 ≤ N)
    (lab : (Fin j → Fin N) → Bool)
    (hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hUc : ∀ d, d ≤ j → Compress ↥U {u : ↥U | (u : X) ∈ V} d)
    (hfar : ∀ m, lab m = true → ∀ x ∈ boxSet m, ∀ i,
      2/(N:ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/(N:ℝ))
    (f : C(IC j, X))
    (hlabU : ∀ m, lab m = false → ∀ x ∈ boxSet m, f x ∈ U)
    (hlabV : ∀ m, lab m = true → ∀ x ∈ boxSet m, f x ∈ V)
    (hbd : ∀ x, x ∈ Cube.boundary (Fin j) → f x ∈ U) :
    ∃ G : C(IC j × I, X),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ U) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hJf : Jinv (U := U) (V := V) lab f := by
    refine ⟨?_, ?_, ?_⟩
    · rintro d ⟨m, hm, hmc⟩ - x hx
      exact hlabV m hm x (hmc hx)
    · rintro d ⟨m, hm, hmc⟩ - x hx
      exact hlabU m hm x (hmc hx)
    · rintro d ⟨m, hm, hmc⟩ ⟨m', hm', hm'c⟩ x hx
      exact ⟨hlabU m' hm' x (hm'c hx), hlabV m hm x (hmc hx)⟩
  obtain ⟨g, H, hJg, hIg⟩ := process_all hN1 hVc hUc f hJf (j + 1) le_rfl
  have hend : ∀ x, g x ∈ U := endgame hN1 hfar hJg hIg
  refine ⟨⟨fun p : IC j × I => H.toHomotopy (p.2, p.1),
    H.toHomotopy.continuous.comp (continuous_snd.prodMk continuous_fst)⟩, ?_, ?_, ?_⟩
  · intro x
    show H.toHomotopy ((0 : I), x) = f x
    exact H.toHomotopy.map_zero_left x
  · intro x hx t
    show H.toHomotopy (t, x) = f x
    exact H.prop' t x hx
  · intro x
    show H.toHomotopy ((1 : I), x) ∈ U
    rw [show H.toHomotopy ((1 : I), x) = g x from H.toHomotopy.map_one_left x]
    exact hend x

end Work.ThomBordism.TwoSet

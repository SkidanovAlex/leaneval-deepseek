import Mathlib
import Submission.Work.RatHurewicz.Triad.Translate
import Submission.Work.RatHurewicz.Triad.exists_preparation
import Submission.Work.RatHurewicz.Triad.Urysohn
import Submission.Work.RatHurewicz.Triad.Convert
import Submission.Work.RatHurewicz.twoSetLabel

/-!
# The final assembly of the triad compression theorem

This file collects the tools that turn the preparation theorem `exists_preparation` and the
Urysohn step `triadUrysohn` into the target `Work.RatHurewicz.triadCompression`:

* `Ffibre_ext` — the elements of the homotopy fibre are determined by their endpoint and path;
* `mem_range_excisionComparison_iff` — the image of the excision comparison map consists of the
  points of the homotopy fibre whose path lies in `B`;
* `exists_curryH` — the currying of a homotopy of admissible maps of the triad to a homotopy of
  maps `Iⁿ → F`;
* `finset_castSucc_extract`, `exists_isSmall_of_con`, `exists_isLarge_of_con` — the exit step:
  the clauses of the grid induction at the owner of a point turn into the count of "small" resp.
  "large" space coordinates that `triadUrysohn` needs;
* `triadCompressionAux` — the whole argument.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.StemsB

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)} {n p q N : ℕ}

section Fibre

theorem Ffibre_ext {x : X} {r r' : Ffibre X C x} (h1 : (r.1.1 : X) = (r'.1.1 : X))
    (h2 : Fpath r = Fpath r') : r = r' := by
  refine Subtype.ext ?_
  refine Prod.ext ?_ ?_
  · exact Subtype.ext h1
  · exact Subtype.ext h2

/-- The first component of the comparison map. -/
theorem fst_excisionComparison (p : Fbase B C x₀) :
    (excisionComparison B C x₀ p).1.1 = interInclRight B C p.1.1 :=
  homotopyFibreMap_fst (interInclLeft B C) (setIncl C) (setIncl B)
    (interInclRight B C) (excision_square B C) x₀ p

/-- **The range of the excision comparison map.**  A point of the homotopy fibre of `C ↪ X` lies in
the image of `excisionComparison B C x₀` exactly when its path lies in `B` (the endpoint is then
automatically in `B ∩ C`). -/
theorem mem_range_excisionComparison_iff (r : Ffibre X C (x₀ : X)) :
    r ∈ Set.range (excisionComparison B C x₀) ↔ ∀ t : I, Fpath r t ∈ B := by
  constructor
  · rintro ⟨p, rfl⟩ t
    have h2 := Fpath_excisionComparison p
    exact h2 ▸ (p.1.2.1 t).2
  · intro h
    have hB1 : (r.1.1 : X) ∈ B := by
      have h1 := h 1
      rwa [Fpath_one] at h1
    have hC1 : (r.1.1 : X) ∈ C := r.1.1.2
    let a : ↥(B ∩ C) := ⟨(r.1.1 : X), hB1, hC1⟩
    let δ : C(I, ↥B) := ⟨fun t => ⟨Fpath r t, h t⟩, (Fpath r).continuous.subtype_mk _⟩
    let γ : PathSpace ↥B (interInclLeft B C x₀) :=
      ⟨δ, by
        show δ 0 = interInclLeft B C x₀
        refine Subtype.ext ?_
        show ((Fpath r 0 : X)) = x₀.1
        rw [Fpath_zero]⟩
    let p : Fbase B C x₀ :=
      ⟨(a, γ), by
        show (evalOne ↥B (interInclLeft B C x₀)) γ = (interInclLeft B C) a
        refine Subtype.ext ?_
        show ((Fpath r 1 : X)) = (a : X)
        rw [Fpath_one]⟩
    refine ⟨p, ?_⟩
    refine Ffibre_ext ?_ ?_
    · refine (congrArg (fun z : ↥C => (z : X)) (fst_excisionComparison p)).trans ?_
      rfl
    · refine (Fpath_excisionComparison p).trans ?_
      refine ContinuousMap.ext fun t => ?_
      show ((setIncl B) (δ t)) = Fpath r t
      rfl

/-- **The currying of a homotopy of admissible maps.**  If `Θ : I^{n+1} × I → X` starts, for every
time `s`, at `x` and ends in `C`, then it curries to a homotopy `Iⁿ × I → F` of maps into the
homotopy fibre of `C ↪ X`, whose path at `(u, s)` is `t ↦ Θ (Fin.snoc u t, s)`. -/
theorem exists_curryH {x : X} (Θ : C(ICube (n + 1) × I, X))
    (h0 : ∀ (u : ICube n) (s : I), Θ (Fin.snoc u 0, s) = x)
    (h1 : ∀ (u : ICube n) (s : I), Θ (Fin.snoc u 1, s) ∈ C) :
    ∃ G : C(ICube n × I, Ffibre X C x),
      (∀ u s t, Fpath (G (u, s)) t = Θ (Fin.snoc u t, s)) ∧
      (∀ u s, (((G (u, s)).1.1 : ↥C) : X) = Θ (Fin.snoc u 1, s)) := by
  classical
  have hsnoc1 : Continuous fun q : (ICube n × I) × I =>
      (Fin.snoc q.1.1 q.2 : ICube (n + 1)) :=
    Continuous.finSnoc (A := fun _ => unitInterval)
      (f := fun q : (ICube n × I) × I => q.1.1)
      (g := fun q : (ICube n × I) × I => q.2)
      (continuous_fst.comp continuous_fst) continuous_snd
  have hsnoc : Continuous fun q : (ICube n × I) × I =>
      ((Fin.snoc q.1.1 q.2 : ICube (n + 1)), q.1.2) :=
    hsnoc1.prodMk (continuous_snd.comp continuous_fst)
  have hfixed : ∀ p : ICube n × I, Continuous fun t : I => Θ (Fin.snoc p.1 t, p.2) := by
    intro p
    have hfx : Continuous fun t : I => (Fin.snoc p.1 t : ICube (n + 1)) :=
      Continuous.finSnoc (A := fun _ => unitInterval) (f := fun _ : I => p.1)
        (g := fun t : I => t) continuous_const continuous_id
    exact Θ.continuous.comp (hfx.prodMk continuous_const)
  have hpath : Continuous (fun p : ICube n × I =>
      (⟨fun t => Θ (Fin.snoc p.1 t, p.2), hfixed p⟩ : C(I, X))) :=
    ContinuousMap.continuous_of_continuous_uncurry
      (fun p : ICube n × I => (⟨fun t => Θ (Fin.snoc p.1 t, p.2), hfixed p⟩ : C(I, X)))
      (Θ.continuous.comp hsnoc)
  have hγ : Continuous fun p : ICube n × I =>
      (⟨⟨fun t => Θ (Fin.snoc p.1 t, p.2), hfixed p⟩, h0 p.1 p.2⟩ : PathSpace X x) :=
    Continuous.subtype_mk hpath _
  have hend : Continuous fun p : ICube n × I =>
      (⟨Θ (Fin.snoc p.1 1, p.2), h1 p.1 p.2⟩ : ↥C) := by
    have h1s : Continuous fun p : ICube n × I => (Fin.snoc p.1 1 : ICube (n + 1)) :=
      Continuous.finSnoc (A := fun _ => unitInterval) (f := fun p : ICube n × I => p.1)
        (g := fun _ : ICube n × I => (1 : I)) continuous_fst continuous_const
    exact Continuous.subtype_mk (Θ.continuous.comp (h1s.prodMk continuous_snd)) _
  have hcompat : ∀ p : ICube n × I,
      (evalOne X x) (⟨⟨fun t => Θ (Fin.snoc p.1 t, p.2), hfixed p⟩, h0 p.1 p.2⟩ :
          PathSpace X x) =
        (setIncl C) (⟨Θ (Fin.snoc p.1 1, p.2), h1 p.1 p.2⟩ : ↥C) := by
    intro p
    rfl
  let Gfun : ICube n × I → Ffibre X C x := fun p =>
    ⟨((⟨Θ (Fin.snoc p.1 1, p.2), h1 p.1 p.2⟩ : ↥C),
      (⟨⟨fun t => Θ (Fin.snoc p.1 t, p.2), hfixed p⟩, h0 p.1 p.2⟩ : PathSpace X x)),
     hcompat p⟩
  have hGcont : Continuous Gfun :=
    Continuous.subtype_mk (Continuous.prodMk hend hγ) _
  refine ⟨⟨Gfun, hGcont⟩, ?_, ?_⟩
  · intro u s t
    rfl
  · intro u s
    rfl

end Fibre

section Exit

/-- From a set of at least `P` indices of `Fin (n+1)` with the `IsSmall` property, one extracts a
set of at least `P - 1` *space* indices of `Fin n` with the same property: at most the last
coordinate is lost. -/
theorem finset_castSucc_extract {n P : ℕ} (Q : Fin (n + 1) → Prop) (L : Finset (Fin (n + 1)))
    (hcard : P ≤ L.card) (hL : ∀ i ∈ L, Q i) :
    ∃ L' : Finset (Fin n), P - 1 ≤ L'.card ∧ ∀ i ∈ L', Q i.castSucc := by
  refine ⟨Finset.univ.filter (fun i : Fin n => i.castSucc ∈ L), ?_, ?_⟩
  · have hsub : L ⊆ (Finset.univ.filter (fun i : Fin n => i.castSucc ∈ L)).image Fin.castSucc
        ∪ {Fin.last n} := by
      intro i hi
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, by simp [hi], rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have h1 : L.card ≤ ((Finset.univ.filter (fun i : Fin n => i.castSucc ∈ L)).image Fin.castSucc
        ∪ {Fin.last n}).card := Finset.card_le_card hsub
    have h2 : ((Finset.univ.filter (fun i : Fin n => i.castSucc ∈ L)).image Fin.castSucc
        ∪ {Fin.last n}).card
        ≤ (Finset.univ.filter (fun i : Fin n => i.castSucc ∈ L)).card + 1 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have himg := Finset.card_image_le
        (s := Finset.univ.filter (fun i : Fin n => i.castSucc ∈ L)) (f := Fin.castSucc)
      simp only [Finset.card_singleton]
      omega
    omega
  · intro i hi
    exact hL i.castSucc (by simpa using hi)

/-- **The `K`-exit.**  At a point where `Ψ` takes a value outside `C`, the clauses of the grid
induction at the owner cell exhibit `p + 1` space coordinates that are "small". -/
theorem exists_isSmall_of_con {Φ Ψ : C(IC (n + 1), X)} (hN : 1 ≤ N)
    (hsub : ∀ c : CellIdx (n + 1) N, CellB B Φ c ∨ CellC C Φ c)
    (hCon : ∀ c : CellIdx (n + 1) N, ConClauses p q B C Φ Ψ c)
    (hVC : ValsC (N := N) C Φ Ψ) :
    ∀ z : IC (n + 1), Ψ z ∉ C →
      ∃ L : Finset (Fin n), p + 1 ≤ L.card ∧ ∀ i ∈ L, IsSmall N z i.castSucc := by
  intro z hz
  have hzc : z ∈ cellSet (cOf N z) := mem_cOf N hN z
  rcases hsub (cOf N z) with hB | hC
  · by_cases hC' : CellC C Φ (cOf N z)
    · exact absurd (hVC _ hC' z hzc) hz
    · obtain ⟨cl1, cl2, -, -⟩ := hCon (cOf N z)
      by_cases hle : cellDim (cOf N z) ≤ p + 1
      · exact absurd (cl1 hB hC' hle z hzc).2 hz
      · obtain ⟨L, hL, hLi⟩ := cl2 hB hC' (by omega) z hzc hz
        obtain ⟨L', hcard, hL'⟩ := finset_castSucc_extract (Q := fun i => IsSmall N z i) L hL
          (fun i hi => isSmall_of_smallIn_cOf (hLi i hi))
        exact ⟨L', by omega, hL'⟩
  · exact absurd (hVC _ hC z hzc) hz

/-- **The `G`-exit.**  At a point where `Ψ` takes a value outside `B`, the clauses of the grid
induction at the owner cell exhibit `q + 1` space coordinates that are "large". -/
theorem exists_isLarge_of_con {Φ Ψ : C(IC (n + 1), X)} (hN : 1 ≤ N)
    (hsub : ∀ c : CellIdx (n + 1) N, CellB B Φ c ∨ CellC C Φ c)
    (hCon : ∀ c : CellIdx (n + 1) N, ConClauses p q B C Φ Ψ c)
    (hVB : ValsB (N := N) B Φ Ψ) :
    ∀ z : IC (n + 1), Ψ z ∉ B →
      ∃ L : Finset (Fin n), q + 1 ≤ L.card ∧ ∀ i ∈ L, IsLarge N z i.castSucc := by
  intro z hz
  have hzc : z ∈ cellSet (cOf N z) := mem_cOf N hN z
  rcases hsub (cOf N z) with hB | hC
  · exact absurd (hVB _ hB z hzc) hz
  · by_cases hB' : CellB B Φ (cOf N z)
    · exact absurd (hVB _ hB' z hzc) hz
    · obtain ⟨-, -, cl3, cl4⟩ := hCon (cOf N z)
      by_cases hle : cellDim (cOf N z) ≤ q + 1
      · exact absurd (cl3 hB' hC hle z hzc).1 hz
      · obtain ⟨L, hL, hLi⟩ := cl4 hB' hC (by omega) z hzc hz
        obtain ⟨L', hcard, hL'⟩ := finset_castSucc_extract (Q := fun i => IsLarge N z i) L hL
          (fun i hi => isLarge_of_largeIn_cOf (hLi i hi))
        exact ⟨L', by omega, hL'⟩

end Exit

section Main

/-- **Puppe's preparation theorem plus the Urysohn step**: the compression property of the pair
`(F, F_B)` of the triad `(X; B, C)` in all dimensions `n ≤ p + q + 1`. -/
theorem triadCompressionAux (hB : IsOpen B) (hC : IsOpen C) (hBC : B ∪ C = Set.univ)
    (x₀ : ↥(B ∩ C)) (p q : ℕ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    {n : ℕ} (hn : n ≤ p + q + 1) :
    CompressRel (homotopyFibre (setIncl C) ⟨x₀.1, x₀.2.2⟩)
      (Set.range (excisionComparison B C x₀)) n := by
  intro f hf
  let Φ : C(IC (n + 1), X) := uncurryF f
  obtain ⟨N, hN, hlab⟩ := twoSetLabel hB hC hBC Φ
  have hadm : TriadAdmissible B C x₀ Φ := triadAdmissible_uncurryF f hf
  obtain ⟨Ψ, Θp, hΘp0, hΘp1, hΘpadm, hCon, hVB, hVC⟩ :=
    exists_preparation (p := p) (q := q) hN hadm hBc hCc hB0 hC0 hlab
  have hK := exists_isSmall_of_con (p := p) (q := q) hN hlab hCon hVC
  have hG := exists_isLarge_of_con (p := p) (q := q) hN hlab hCon hVB
  have hΨadm : TriadAdmissible B C x₀ Ψ := by
    obtain ⟨h1, h2, h3⟩ := hΘpadm 1
    exact ⟨fun u => by simpa only [sliceOf_apply, hΘp1] using h1 u,
      fun u => by simpa only [sliceOf_apply, hΘp1] using h2 u,
      fun u hu t => by simpa only [sliceOf_apply, hΘp1] using h3 u hu t⟩
  obtain ⟨Θu, hΘu0, hΘuslice, hΘuB⟩ :=
    triadUrysohn hB hC hBC x₀ p q n hn N hN Ψ hΨadm.1 hΨadm.2.1 hΨadm.2.2 hK hG
  have hjoin : ∀ z : IC (n + 1), Θp (z, 1) = Θu (z, 0) := fun z => by rw [hΘp1, hΘu0]
  obtain ⟨Θc, hΘc0, hΘc1, hΘcleft, hΘcright⟩ := homotopyConcat (G₁ := Θp) (G₂ := Θu) hjoin
  have hΦun : ∀ z : IC (n + 1), Φ z = uncurryF f z := fun _ => rfl
  have hΘc00 : ∀ z : IC (n + 1), Θc (z, 0) = uncurryF f z := fun z => by
    rw [hΘc0, hΘp0, hΦun]
  have hslice : ∀ s : I, TriadAdmissible B C x₀ (sliceOf Θc s) := by
    intro s
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · have hEq : sliceOf Θc s = sliceOf Θp (phiOne s) :=
        ContinuousMap.ext fun z => hΘcleft s hs z
      rw [hEq]; exact hΘpadm (phiOne s)
    · have hs' : 1 / 2 ≤ (s : ℝ) := le_of_lt (not_le.mp hs)
      have hEq : sliceOf Θc s = sliceOf Θu (phiTwo s) :=
        ContinuousMap.ext fun z => hΘcright s hs' z
      rw [hEq]; exact hΘuslice (phiTwo s)
  obtain ⟨G, hGpath, hGend⟩ := exists_curryH (x := (x₀ : X)) Θc
    (fun u s => (hslice s).1 u) (fun u s => (hslice s).2.1 u)
  have hG0 : ∀ u : ICube n, G (u, 0) = f u := by
    intro u
    refine Ffibre_ext ?_ ?_
    · rw [hGend u 0, hΘc00, uncurryF_snoc]
      exact Fpath_one (f u)
    · refine ContinuousMap.ext fun t => ?_
      rw [hGpath u 0 t, hΘc00, uncurryF_snoc]
      rfl
  have hGbd : ∀ (u : ICube n), u ∈ Cube.boundary (Fin n) → ∀ s : I,
      G (u, s) ∈ Set.range (excisionComparison B C x₀) := by
    intro u hu s
    exact (mem_range_excisionComparison_iff (G (u, s))).mpr fun t => by
      rw [hGpath u s t]; exact (hslice s).2.2 u hu t
  have hG1 : ∀ u : ICube n, G (u, 1) ∈ Set.range (excisionComparison B C x₀) := by
    intro u
    exact (mem_range_excisionComparison_iff (G (u, 1))).mpr fun t => by
      rw [hGpath u 1 t, hΘc1]; exact hΘuB _
  exact compressRel_of_homotopyPairs f G hG0 hGbd hG1

end Main

end

end Work.RatHurewicz.Triad

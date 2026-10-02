import Mathlib
import Submission.Work.Serre.E2bDefs
import Submission.Work.Serre.SHatData
import Submission.Work.Serre.sHatExtend

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# From the compression hypothesis to the coherent family of homotopies

`Work.Serre.simpHom_of_compress`: the compression hypothesis `CompressHyp X A N` (every map of
pairs `(Iᵏ,∂Iᵏ) → (X,A)`, `k ≤ N`, is homotopic into `A` relative to the boundary) produces a
coherent family `SimpHom X A N` of homotopies of singular simplices.

The construction is the skeleton-by-skeleton one: the homotopy of an `n`-simplex is prescribed on
the *hat* `sHat n = (Δⁿ × {0}) ∪ (∂Δⁿ × I)` by the homotopies of its faces (glued together in
`Work.Serre.exists_sHatData` and its `n = 1` companion `Work.Serre.exists_sHatData_one`) and then
extended by `Work.Serre.sHatExtend`, which uses the compression property in dimension `n`.

* `Work.Serre.constHomotopy` — the trivial homotopy of a simplex;
* `Work.Serre.coface_coface` — the cosimplicial identity `δ_j δ_i = δ_i δ_{j-1}` (`i < j`);
* `Work.Serre.exists_sHatData_one` — the glue in dimension one (only corner conditions);
* `Work.Serre.simpHom_succ` — adding one top level to a `SimpHom`;
* `Work.Serre.simpHom_zero`, `Work.Serre.simpHom_one`, `Work.Serre.simpHom_step` — the levelwise
  constructions;
* `Work.Serre.simpHom_of_compress` — the induction.
-/

open scoped Topology unitInterval
open Work.Stems.Cubical

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

variable {X : Type} [TopologicalSpace X] {A : Set X}

/-- The trivial homotopy of a singular simplex (constant in time). -/
def constHomotopy {n : ℕ} (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) :
    C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, X) where
  toFun p := s p.1
  continuous_toFun := s.continuous.comp continuous_fst

@[simp]
theorem constHomotopy_apply {n : ℕ} (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X))
    (z : ↥(stdSimplex ℝ (Fin (n + 1)))) (t : unitInterval) : constHomotopy s (z, t) = s z :=
  rfl

/-- **The cosimplicial identity `δ_j ∘ δ_i = δ_i ∘ δ_{j-1}`** for `i < j` (as maps
`Δ^{m} → Δ^{m+2}`). -/
theorem coface_coface {m : ℕ} (i j : Fin (m + 3)) (hij : i < j) :
    (coface (m + 1) j).comp (coface m ⟨i.val, by omega⟩) =
      (coface (m + 1) i).comp (coface m ⟨j.val - 1, by omega⟩) := by
  ext z
  simp only [ContinuousMap.comp_apply, coface_apply, stdSimplex.map_comp_apply]
  rw [show (Fin.succAbove j ∘ Fin.succAbove ⟨i.val, by omega⟩ : Fin (m + 1) → Fin (m + 3))
      = (Fin.succAbove i ∘ Fin.succAbove ⟨j.val - 1, by omega⟩) from
    funext fun l => (succAbove_succAbove i j hij l).symm]

/-- **Extending a `SimpHom` by one level.**  Given `H : SimpHom X A N` and the data `F` of the
homotopies of the `(N+1)`-simplices, compatible with `H` on the faces (`hside`) and with the
simplices already in `A` (`hconst`), one gets `SimpHom X A (N+1)`. -/
def simpHom_succ {N : ℕ} (H : SimpHom X A N)
    (F : C(↥(stdSimplex ℝ (Fin (N + 2))), X) →
      C(↥(stdSimplex ℝ (Fin (N + 2))) × unitInterval, X))
    (ht0 : ∀ (s : C(↥(stdSimplex ℝ (Fin (N + 2))), X))
      (z : ↥(stdSimplex ℝ (Fin (N + 2)))), F s (z, 0) = s z)
    (htop : ∀ (s : C(↥(stdSimplex ℝ (Fin (N + 2))), X))
      (z : ↥(stdSimplex ℝ (Fin (N + 2)))), F s (z, 1) ∈ A)
    (hconst : ∀ (s : C(↥(stdSimplex ℝ (Fin (N + 2))), X)), (∀ z, s z ∈ A) →
      ∀ (z : ↥(stdSimplex ℝ (Fin (N + 2)))) (t : unitInterval), F s (z, t) = s z)
    (hside : ∀ (s : C(↥(stdSimplex ℝ (Fin (N + 2))), X)) (i : Fin (N + 2))
      (x : ↥(stdSimplex ℝ (Fin (N + 1)))) (t : unitInterval),
      F s ((coface N i) x, t) = H.G N (s.comp (coface N i)) (x, t)) :
    SimpHom X A (N + 1) := by
  classical
  let G' : ∀ n, C(↥(stdSimplex ℝ (Fin (n + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, X) := fun n =>
    if h : n = N + 1 then h.symm ▸ F else H.G n
  have hG'₀ : ∀ (n : ℕ) (hn : n ≠ N + 1), G' n = H.G n := by
    intro n hn
    simp only [G', dif_neg hn]
  have hG'₁ : G' (N + 1) = F := by
    simp only [G', dif_pos rfl]
  refine ⟨G', ?_, ?_, ?_, ?_⟩
  · intro n hn s z
    by_cases h : n = N + 1
    · subst h
      rw [hG'₁]
      exact ht0 s z
    · rw [hG'₀ n h]
      exact H.ht0 n (by omega) s z
  · intro n hn s i x t
    by_cases h : n = N
    · subst n
      rw [hG'₁, hG'₀ N (by omega)]
      exact hside s i x t
    · rw [hG'₀ (n + 1) (by omega), hG'₀ n (by omega)]
      exact H.hside n (by omega) s i x t
  · intro n hn s z
    by_cases h : n = N + 1
    · subst h
      rw [hG'₁]
      exact htop s z
    · rw [hG'₀ n h]
      exact H.htop n (by omega) s z
  · intro n hn s hs z t
    by_cases h : n = N + 1
    · subst h
      rw [hG'₁]
      exact hconst s hs z t
    · rw [hG'₀ n h]
      exact H.hconst n (by omega) s hs z t

/-! ## The glue in dimension one -/

/-- The simplex point of a point of the hat `sHat n`. -/
def hatSimplex (n : ℕ) (q : ↥(sHat n)) : ↥(stdSimplex ℝ (Fin (n + 1))) := q.1.1

/-- The time coordinate of a point of the hat `sHat n`. -/
def hatTime (n : ℕ) (q : ↥(sHat n)) : unitInterval := q.1.2

theorem continuous_hatSimplex (n : ℕ) : Continuous (hatSimplex n) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_hatTime (n : ℕ) : Continuous (hatTime n) :=
  continuous_snd.comp continuous_subtype_val

/-- **Gluing the data of a `1`-simplex hat.**  In dimension one the hat
`sHat 1 = (Δ¹ × {0}) ∪ (∂Δ¹ × I)` has two side pieces (at the two vertices) and one bottom piece;
the only compatibility required is at the two corners, which is the hypothesis `h0`. -/
theorem exists_sHatData_one
    (G : (i : Fin 2) → C(↥(stdSimplex ℝ (Fin 1)) × unitInterval, X))
    (s : C(↥(stdSimplex ℝ (Fin 2)), X))
    (h0 : ∀ (i : Fin 2) (x : ↥(stdSimplex ℝ (Fin 1))), G i (x, 0) = s ((coface 0 i) x)) :
    ∃ f : C(↥(sHat 1), X),
      (∀ q : ↥(sHat 1), hatTime 1 q = 0 → f q = s (hatSimplex 1 q)) ∧
      (∀ (i : Fin 2) (q : ↥(sHat 1)) (h : (hatSimplex 1 q).1 i = 0),
        f q = G i (⟨uncoface 0 i (hatSimplex 1 q), uncoface_mem 0 i (hatSimplex 1 q) h⟩,
          hatTime 1 q)) := by
  classical
  let junk : ↥(stdSimplex ℝ (Fin 1)) := stdSimplex.vertex 0
  let side : (i : Fin 2) → ↥(sHat 1) → X := fun i q =>
    G i (if h : (hatSimplex 1 q).1 i = 0
      then ⟨uncoface 0 i (hatSimplex 1 q), uncoface_mem 0 i (hatSimplex 1 q) h⟩
      else junk, hatTime 1 q)
  let ffun : ↥(sHat 1) → X := fun q =>
    if h : (hatSimplex 1 q).1 0 = 0 then side 0 q
    else if h' : (hatSimplex 1 q).1 1 = 0 then side 1 q
    else s (hatSimplex 1 q)
  have hside_eq : ∀ (i : Fin 2) (q : ↥(sHat 1)) (h : (hatSimplex 1 q).1 i = 0),
      side i q = G i (⟨uncoface 0 i (hatSimplex 1 q), uncoface_mem 0 i (hatSimplex 1 q) h⟩,
        hatTime 1 q) := by
    intro i q h
    simp only [side, dif_pos h]
  have hbottom : ∀ q : ↥(sHat 1), hatTime 1 q = 0 → ffun q = s (hatSimplex 1 q) := by
    intro q ht
    rcases eq_or_ne ((hatSimplex 1 q).1 0) 0 with h00 | h00
    · simp only [ffun, dif_pos h00, hside_eq 0 q h00, ht,
        h0 0 ⟨uncoface 0 0 (hatSimplex 1 q), uncoface_mem 0 0 (hatSimplex 1 q) h00⟩,
        coface_uncoface 0 0 (hatSimplex 1 q) h00]
    · by_cases h11 : (hatSimplex 1 q).1 1 = 0
      · simp only [ffun, dif_neg h00, dif_pos h11, hside_eq 1 q h11, ht,
          h0 1 ⟨uncoface 0 1 (hatSimplex 1 q), uncoface_mem 0 1 (hatSimplex 1 q) h11⟩,
          coface_uncoface 0 1 (hatSimplex 1 q) h11]
      · simp only [ffun, dif_neg h00, dif_neg h11]
  have hffun_side : ∀ (i : Fin 2) (q : ↥(sHat 1)) (h : (hatSimplex 1 q).1 i = 0),
      ffun q = side i q := by
    intro i q h
    have hi : i = 0 ∨ i = 1 := by
      rcases (by omega : i.val = 0 ∨ i.val = 1) with hi0 | hi1
      · exact Or.inl (Fin.ext (by simpa using hi0))
      · exact Or.inr (Fin.ext (by simpa using hi1))
    rcases hi with rfl | rfl
    · simp only [ffun, dif_pos h]
    · have h00 : ¬ ((hatSimplex 1 q).1 0 = 0) := by
        intro h00
        have hsum := (hatSimplex 1 q).2.2
        rw [Fin.sum_univ_two] at hsum
        linarith
      simp only [ffun, dif_neg h00, dif_pos h]
  have hptCont : Continuous (fun q : ↥(sHat 1) => ((hatSimplex 1 q).1 : Fin 2 → ℝ)) :=
    continuous_subtype_val.comp (continuous_hatSimplex 1)
  have hset0 : IsClosed {q : ↥(sHat 1) | (hatSimplex 1 q).1 0 = 0} :=
    isClosed_eq ((continuous_apply 0).comp hptCont) continuous_const
  have hset1 : IsClosed {q : ↥(sHat 1) | (hatSimplex 1 q).1 1 = 0} :=
    isClosed_eq ((continuous_apply 1).comp hptCont) continuous_const
  have hsetT : IsClosed {q : ↥(sHat 1) | hatTime 1 q = 0} :=
    isClosed_eq (continuous_hatTime 1) continuous_const
  have hsidecont : ∀ i : Fin 2,
      ContinuousOn (side i) {q : ↥(sHat 1) | (hatSimplex 1 q).1 i = 0} := by
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have hpiece : ∀ q : ↥{q : ↥(sHat 1) | (hatSimplex 1 q).1 i = 0},
        side i q.1 = G i (⟨uncoface 0 i (hatSimplex 1 q.1),
          uncoface_mem 0 i (hatSimplex 1 q.1) q.2⟩, hatTime 1 q.1) := by
      intro q
      have hcond : (hatSimplex 1 q.1).1 i = 0 := q.2
      simp only [side]
      rw [dif_pos hcond]
    refine Continuous.congr ?_ (fun q => (hpiece q).symm)
    refine (G i).continuous.comp (Continuous.prodMk ?_ ?_)
    · refine Continuous.subtype_mk (f := fun q : ↥{q : ↥(sHat 1) | (hatSimplex 1 q).1 i = 0} =>
        uncoface 0 i (hatSimplex 1 q.1)) ?_ _
      refine continuous_pi (fun j => ?_)
      exact (continuous_apply (Fin.succAbove i j)).comp
        ((continuous_subtype_val.comp (continuous_hatSimplex 1)).comp continuous_subtype_val)
    · exact (continuous_hatTime 1).comp continuous_subtype_val
  have hcont : Continuous ffun := by
    rw [continuous_iff_isClosed]
    intro T hT
    have hsub : ffun ⁻¹' T =
        (({q : ↥(sHat 1) | (hatSimplex 1 q).1 0 = 0} ∩ side 0 ⁻¹' T)
          ∪ ({q : ↥(sHat 1) | (hatSimplex 1 q).1 1 = 0} ∩ side 1 ⁻¹' T))
        ∪ ({q : ↥(sHat 1) | hatTime 1 q = 0} ∩
            (fun q : ↥(sHat 1) => s (hatSimplex 1 q)) ⁻¹' T) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro q hq
        rw [Set.mem_preimage] at hq
        by_cases h00 : (hatSimplex 1 q).1 0 = 0
        · refine Or.inl (Or.inl ⟨h00, ?_⟩)
          rw [Set.mem_preimage]
          rw [show side 0 q = ffun q from (hffun_side 0 q h00).symm]
          exact hq
        · by_cases h11 : (hatSimplex 1 q).1 1 = 0
          · refine Or.inl (Or.inr ⟨h11, ?_⟩)
            rw [Set.mem_preimage]
            rw [show side 1 q = ffun q from (hffun_side 1 q h11).symm]
            exact hq
          · have ht : hatTime 1 q = 0 :=
              (show hatTime 1 q = 0 ∨ hatSimplex 1 q ∈ simplexBdry 1 from q.2).elim id
                (fun hb => by
                  obtain ⟨k, hk⟩ := hb
                  have hne : ∀ j : Fin 2, (hatSimplex 1 q).1 j ≠ 0 :=
                    Fin.forall_fin_two.2 ⟨h00, h11⟩
                  exact absurd hk (hne k))
            refine Or.inr ⟨ht, ?_⟩
            rw [Set.mem_preimage]
            rw [show s (hatSimplex 1 q) = ffun q from (hbottom q ht).symm]
            exact hq
      · refine Set.union_subset (Set.union_subset ?_ ?_) ?_
        · rintro q ⟨h00, hq⟩
          rw [Set.mem_preimage] at hq ⊢
          rw [show ffun q = side 0 q from hffun_side 0 q h00]
          exact hq
        · rintro q ⟨h11, hq⟩
          rw [Set.mem_preimage] at hq ⊢
          rw [show ffun q = side 1 q from hffun_side 1 q h11]
          exact hq
        · rintro q ⟨ht, hq⟩
          rw [Set.mem_preimage] at hq ⊢
          rw [show ffun q = s (hatSimplex 1 q) from hbottom q ht]
          exact hq
    rw [hsub]
    refine IsClosed.union (IsClosed.union ?_ ?_) ?_
    · obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hsidecont 0)) T hT
      have hset : {q : ↥(sHat 1) | (hatSimplex 1 q).1 0 = 0} ∩ side 0 ⁻¹' T
          = U ∩ {q : ↥(sHat 1) | (hatSimplex 1 q).1 0 = 0} := by
        rw [Set.inter_comm, hUeq]
      rw [hset]
      exact hU.inter hset0
    · obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hsidecont 1)) T hT
      have hset : {q : ↥(sHat 1) | (hatSimplex 1 q).1 1 = 0} ∩ side 1 ⁻¹' T
          = U ∩ {q : ↥(sHat 1) | (hatSimplex 1 q).1 1 = 0} := by
        rw [Set.inter_comm, hUeq]
      rw [hset]
      exact hU.inter hset1
    · exact hsetT.inter (hT.preimage (s.continuous.comp (continuous_hatSimplex 1)))
  exact ⟨⟨ffun, hcont⟩,
    fun q ht => hbottom q ht,
    fun i q h => by
      change ffun q = G i (⟨uncoface 0 i (hatSimplex 1 q),
        uncoface_mem 0 i (hatSimplex 1 q) h⟩, hatTime 1 q)
      rw [hffun_side i q h, hside_eq i q h]⟩

/-! ## The levelwise constructions -/

/-- **Level 0**: a `0`-simplex is a point, so `CompressRel X A 0` provides its homotopy. -/
def simpHom_zero (hc : Work.RatHurewicz.CompressRel X A 0) : SimpHom X A 0 := by
  classical
  have hpath : ∀ s : C(↥(stdSimplex ℝ (Fin 1)), X),
      ∃ G : C(↥(stdSimplex ℝ (Fin 1)) × unitInterval, X),
        (∀ z, G (z, 0) = s z) ∧ (∀ z, G (z, 1) ∈ A) := by
    intro s
    have hb : ∀ x : IC 0, x ∈ Cube.boundary (Fin 0) →
        (s.comp ⟨fun _ => stdSimplex.vertex (0 : Fin 1), continuous_const⟩) x ∈ A :=
      fun x hx => absurd hx (by rintro ⟨i, -⟩; exact Fin.elim0 i)
    obtain ⟨G', h0, -, h1⟩ :=
      hc (s.comp ⟨fun _ => stdSimplex.vertex (0 : Fin 1), continuous_const⟩) hb
    refine ⟨⟨fun p => G' (fun _ => 0, p.2), ?_⟩, ?_, ?_⟩
    · exact G'.continuous.comp (Continuous.prodMk continuous_const continuous_snd)
    · intro z
      show G' (fun _ => 0, (0 : unitInterval)) = s z
      rw [h0]
      exact congrArg s (Subsingleton.elim _ _)
    · intro z
      exact h1 _
  let F0 : C(↥(stdSimplex ℝ (Fin 1)), X) →
      C(↥(stdSimplex ℝ (Fin 1)) × unitInterval, X) :=
    fun s => if h : ∀ z, s z ∈ A then constHomotopy s else Classical.choose (hpath s)
  have hF0_ht0 : ∀ (s : C(↥(stdSimplex ℝ (Fin 1)), X))
      (z : ↥(stdSimplex ℝ (Fin 1))), F0 s (z, 0) = s z := by
    intro s z
    by_cases h : ∀ z, s z ∈ A
    · simp only [F0, dif_pos h, constHomotopy_apply]
    · simp only [F0, dif_neg h]
      exact (Classical.choose_spec (hpath s)).1 z
  have hF0_htop : ∀ (s : C(↥(stdSimplex ℝ (Fin 1)), X))
      (z : ↥(stdSimplex ℝ (Fin 1))), F0 s (z, 1) ∈ A := by
    intro s z
    by_cases h : ∀ z, s z ∈ A
    · simp only [F0, dif_pos h, constHomotopy_apply]
      exact h z
    · simp only [F0, dif_neg h]
      exact (Classical.choose_spec (hpath s)).2 z
  have hF0_const : ∀ (s : C(↥(stdSimplex ℝ (Fin 1)), X)), (∀ z, s z ∈ A) →
      ∀ (z : ↥(stdSimplex ℝ (Fin 1))) (t : unitInterval), F0 s (z, t) = s z := by
    intro s h z t
    simp only [F0, dif_pos h, constHomotopy_apply]
  let G : ∀ n, C(↥(stdSimplex ℝ (Fin (n + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, X) := fun n =>
    Nat.rec (motive := fun n => C(↥(stdSimplex ℝ (Fin (n + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, X)) F0
      (fun _ _ => fun s => constHomotopy s) n
  have hG0 : G 0 = F0 := rfl
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro n hn s z
    have hn' : n = 0 := by omega
    subst hn'
    rw [hG0]
    exact hF0_ht0 s z
  · intro n hn s i x t
    omega
  · intro n hn s z
    have hn' : n = 0 := by omega
    subst hn'
    rw [hG0]
    exact hF0_htop s z
  · intro n hn s hs z t
    have hn' : n = 0 := by omega
    subst hn'
    rw [hG0]
    exact hF0_const s hs z t

/-- **Level 1**: the homotopies of the `1`-simplices (glue on the hat, then extend). -/
def simpHom_one (H0 : SimpHom X A 0) (hc : Work.RatHurewicz.CompressRel X A 1) :
    SimpHom X A 1 := by
  classical
  have hdata : ∀ s : C(↥(stdSimplex ℝ (Fin 2)), X),
      ∃ F : C(↥(stdSimplex ℝ (Fin 2)) × unitInterval, X),
        (∀ z, F (z, 0) = s z) ∧ (∀ z, F (z, 1) ∈ A) ∧
        (∀ (i : Fin 2) (x : ↥(stdSimplex ℝ (Fin 1))) (t : unitInterval),
          F ((coface 0 i) x, t) = H0.G 0 (s.comp (coface 0 i)) (x, t)) := by
    intro s
    by_cases hA : ∀ z, s z ∈ A
    · refine ⟨constHomotopy s, fun z => rfl, fun z => hA z, ?_⟩
      intro i x t
      simp only [constHomotopy_apply]
      exact (H0.hconst 0 le_rfl (s.comp (coface 0 i)) (fun z => hA _) x t).symm
    · have h0 : ∀ (i : Fin 2) (x : ↥(stdSimplex ℝ (Fin 1))),
          H0.G 0 (s.comp (coface 0 i)) (x, 0) = s ((coface 0 i) x) := by
        intro i x
        rw [H0.ht0 0 le_rfl (s.comp (coface 0 i)) x]
        rfl
      obtain ⟨f, hf0, hfi⟩ := exists_sHatData_one (fun i => H0.G 0 (s.comp (coface 0 i))) s h0
      have hfbdry : ∀ q : ↥(sHat 1),
          (q : ↥(stdSimplex ℝ (Fin 2)) × unitInterval) ∈ sHatBdry 1 → f q ∈ A := by
        intro q hq
        obtain ⟨hb, ht⟩ := hq
        obtain ⟨i, hi⟩ := hb
        rw [hfi i q hi]
        have htime : hatTime 1 q = 1 := ht
        rw [htime]
        exact H0.htop 0 le_rfl (s.comp (coface 0 i)) _
      obtain ⟨F, hFhat, hFtop⟩ := sHatExtend (n := 1) le_rfl hc f hfbdry
      refine ⟨F, ?_, hFtop, ?_⟩
      · intro z
        have hq : (((z, (0 : unitInterval))) : ↥(stdSimplex ℝ (Fin 2)) × unitInterval) ∈ sHat 1 :=
          Or.inl rfl
        rw [hFhat ⟨(z, 0), hq⟩]
        exact hf0 ⟨(z, 0), hq⟩ rfl
      · intro i x t
        have hq : ((((coface 0 i) x, t)) : ↥(stdSimplex ℝ (Fin 2)) × unitInterval) ∈ sHat 1 :=
          Or.inr (coface_mem_simplexBdry i x)
        rw [hFhat ⟨_, hq⟩]
        rw [hfi i ⟨_, hq⟩ (coface_apply_self 0 i x)]
        exact congrArg (fun w => H0.G 0 (s.comp (coface 0 i)) (w, t))
          (Subtype.ext (uncoface_coface 0 i x))
  let F1 : C(↥(stdSimplex ℝ (Fin 2)), X) → C(↥(stdSimplex ℝ (Fin 2)) × unitInterval, X) :=
    fun s => if h : ∀ z, s z ∈ A then constHomotopy s else Classical.choose (hdata s)
  have hF1_ht0 : ∀ (s : C(↥(stdSimplex ℝ (Fin 2)), X))
      (z : ↥(stdSimplex ℝ (Fin 2))), F1 s (z, 0) = s z := by
    intro s z
    by_cases h : ∀ z, s z ∈ A
    · simp only [F1, dif_pos h, constHomotopy_apply]
    · simp only [F1, dif_neg h]
      exact (Classical.choose_spec (hdata s)).1 z
  have hF1_htop : ∀ (s : C(↥(stdSimplex ℝ (Fin 2)), X))
      (z : ↥(stdSimplex ℝ (Fin 2))), F1 s (z, 1) ∈ A := by
    intro s z
    by_cases h : ∀ z, s z ∈ A
    · simp only [F1, dif_pos h, constHomotopy_apply]
      exact h z
    · simp only [F1, dif_neg h]
      exact (Classical.choose_spec (hdata s)).2.1 z
  have hF1_const : ∀ (s : C(↥(stdSimplex ℝ (Fin 2)), X)), (∀ z, s z ∈ A) →
      ∀ (z : ↥(stdSimplex ℝ (Fin 2))) (t : unitInterval), F1 s (z, t) = s z := by
    intro s h z t
    simp only [F1, dif_pos h, constHomotopy_apply]
  have hF1_side : ∀ (s : C(↥(stdSimplex ℝ (Fin 2)), X)) (i : Fin 2)
      (x : ↥(stdSimplex ℝ (Fin 1))) (t : unitInterval),
      F1 s ((coface 0 i) x, t) = H0.G 0 (s.comp (coface 0 i)) (x, t) := by
    intro s i x t
    by_cases h : ∀ z, s z ∈ A
    · simp only [F1, dif_pos h, constHomotopy_apply]
      exact (H0.hconst 0 le_rfl (s.comp (coface 0 i)) (fun z => h _) x t).symm
    · simp only [F1, dif_neg h]
      exact (Classical.choose_spec (hdata s)).2.2 i x t
  exact simpHom_succ H0 F1 hF1_ht0 hF1_htop hF1_const hF1_side

/-- **The induction step**: from the homotopies of the `(k+1)`-simplices to those of the
`(k+2)`-simplices. -/
def simpHom_step (k : ℕ) (H : SimpHom X A (k + 1))
    (hc : Work.RatHurewicz.CompressRel X A (k + 2)) : SimpHom X A (k + 2) := by
  classical
  have hdata : ∀ s : C(↥(stdSimplex ℝ (Fin (k + 3))), X),
      ∃ F : C(↥(stdSimplex ℝ (Fin (k + 3))) × unitInterval, X),
        (∀ z, F (z, 0) = s z) ∧ (∀ z, F (z, 1) ∈ A) ∧
        (∀ (i : Fin (k + 3)) (x : ↥(stdSimplex ℝ (Fin (k + 2)))) (t : unitInterval),
          F ((coface (k + 1) i) x, t) = H.G (k + 1) (s.comp (coface (k + 1) i)) (x, t)) := by
    intro s
    by_cases hA : ∀ z, s z ∈ A
    · refine ⟨constHomotopy s, fun z => rfl, fun z => hA z, ?_⟩
      intro i x t
      simp only [constHomotopy_apply]
      exact (H.hconst (k + 1) le_rfl (s.comp (coface (k + 1) i)) (fun z => hA _) x t).symm
    · have hface : ∀ (i j : Fin (k + 3)) (hij : i < j),
          ((H.G (k + 1) (s.comp (coface (k + 1) j))).comp
              ((coface k ⟨i.val, by omega⟩).prodMap (ContinuousMap.id unitInterval)))
            = ((H.G (k + 1) (s.comp (coface (k + 1) i))).comp
              ((coface k ⟨j.val - 1, by omega⟩).prodMap (ContinuousMap.id unitInterval))) := by
        intro i j hij
        ext p
        obtain ⟨x, t⟩ := p
        show H.G (k + 1) (s.comp (coface (k + 1) j)) ((coface k ⟨i.val, by omega⟩) x, t)
            = H.G (k + 1) (s.comp (coface (k + 1) i))
                ((coface k ⟨j.val - 1, by omega⟩) x, t)
        rw [H.hside k (by omega) (s.comp (coface (k + 1) j)) ⟨i.val, by omega⟩ x t,
          H.hside k (by omega) (s.comp (coface (k + 1) i)) ⟨j.val - 1, by omega⟩ x t]
        have harg : (s.comp (coface (k + 1) j)).comp (coface k ⟨i.val, by omega⟩)
            = (s.comp (coface (k + 1) i)).comp (coface k ⟨j.val - 1, by omega⟩) := by
          rw [ContinuousMap.comp_assoc, coface_coface i j hij, ← ContinuousMap.comp_assoc]
        rw [harg]
      have h0 : ∀ (i : Fin (k + 3)) (x : ↥(stdSimplex ℝ (Fin (k + 2)))),
          H.G (k + 1) (s.comp (coface (k + 1) i)) (x, 0) = s ((coface (k + 1) i) x) := by
        intro i x
        rw [H.ht0 (k + 1) le_rfl (s.comp (coface (k + 1) i)) x]
        rfl
      obtain ⟨f, hf0, hfi⟩ := exists_sHatData (k := k)
        (fun i => H.G (k + 1) (s.comp (coface (k + 1) i))) s hface h0
      have hfbdry : ∀ q : ↥(sHat (k + 2)),
          (q : ↥(stdSimplex ℝ (Fin (k + 3))) × unitInterval) ∈ sHatBdry (k + 2) → f q ∈ A := by
        intro q hq
        obtain ⟨hb, ht⟩ := hq
        obtain ⟨i, hi⟩ := hb
        rw [hfi i q hi]
        have htime : hatTm q = 1 := ht
        rw [htime]
        exact H.htop (k + 1) le_rfl (s.comp (coface (k + 1) i)) _
      obtain ⟨F, hFhat, hFtop⟩ := sHatExtend (n := k + 2) (by omega) hc f hfbdry
      refine ⟨F, ?_, hFtop, ?_⟩
      · intro z
        have hq : (((z, (0 : unitInterval))) : ↥(stdSimplex ℝ (Fin (k + 3))) × unitInterval)
            ∈ sHat (k + 2) := Or.inl rfl
        rw [hFhat ⟨(z, 0), hq⟩]
        exact hf0 ⟨(z, 0), hq⟩ rfl
      · intro i x t
        have hq : ((((coface (k + 1) i) x, t)) : ↥(stdSimplex ℝ (Fin (k + 3))) × unitInterval)
            ∈ sHat (k + 2) := Or.inr (coface_mem_simplexBdry i x)
        rw [hFhat ⟨_, hq⟩]
        rw [hfi i ⟨_, hq⟩ (coface_apply_self (k + 1) i x)]
        exact congrArg (fun w => H.G (k + 1) (s.comp (coface (k + 1) i)) (w, t))
          (Subtype.ext (uncoface_coface (k + 1) i x))
  let Fk : C(↥(stdSimplex ℝ (Fin (k + 3))), X) →
      C(↥(stdSimplex ℝ (Fin (k + 3))) × unitInterval, X) :=
    fun s => if h : ∀ z, s z ∈ A then constHomotopy s else Classical.choose (hdata s)
  have hFk_ht0 : ∀ (s : C(↥(stdSimplex ℝ (Fin (k + 3))), X))
      (z : ↥(stdSimplex ℝ (Fin (k + 3)))), Fk s (z, 0) = s z := by
    intro s z
    by_cases h : ∀ z, s z ∈ A
    · simp only [Fk, dif_pos h, constHomotopy_apply]
    · simp only [Fk, dif_neg h]
      exact (Classical.choose_spec (hdata s)).1 z
  have hFk_htop : ∀ (s : C(↥(stdSimplex ℝ (Fin (k + 3))), X))
      (z : ↥(stdSimplex ℝ (Fin (k + 3)))), Fk s (z, 1) ∈ A := by
    intro s z
    by_cases h : ∀ z, s z ∈ A
    · simp only [Fk, dif_pos h, constHomotopy_apply]
      exact h z
    · simp only [Fk, dif_neg h]
      exact (Classical.choose_spec (hdata s)).2.1 z
  have hFk_const : ∀ (s : C(↥(stdSimplex ℝ (Fin (k + 3))), X)), (∀ z, s z ∈ A) →
      ∀ (z : ↥(stdSimplex ℝ (Fin (k + 3)))) (t : unitInterval), Fk s (z, t) = s z := by
    intro s h z t
    simp only [Fk, dif_pos h, constHomotopy_apply]
  have hFk_side : ∀ (s : C(↥(stdSimplex ℝ (Fin (k + 3))), X)) (i : Fin (k + 3))
      (x : ↥(stdSimplex ℝ (Fin (k + 2)))) (t : unitInterval),
      Fk s ((coface (k + 1) i) x, t) = H.G (k + 1) (s.comp (coface (k + 1) i)) (x, t) := by
    intro s i x t
    by_cases h : ∀ z, s z ∈ A
    · simp only [Fk, dif_pos h, constHomotopy_apply]
      exact (H.hconst (k + 1) le_rfl (s.comp (coface (k + 1) i)) (fun z => h _) x t).symm
    · simp only [Fk, dif_neg h]
      exact (Classical.choose_spec (hdata s)).2.2 i x t
  exact simpHom_succ H Fk hFk_ht0 hFk_htop hFk_const hFk_side

/-- The levelwise construction of the coherent family. -/
def simpHomOf : (N : ℕ) → CompressHyp X A N → SimpHom X A N
  | 0, h => simpHom_zero (h 0 le_rfl)
  | 1, h => simpHom_one (simpHom_zero (h 0 (by omega))) (h 1 le_rfl)
  | k + 2, h => simpHom_step k (simpHomOf (k + 1) (fun m hm => h m (by omega)))
      (h (k + 2) le_rfl)

/-- **From the compression hypothesis to the coherent family of homotopies.** -/
theorem simpHom_of_compress (N : ℕ) (h : CompressHyp X A N) :
    Nonempty (SimpHom X A N) :=
  ⟨simpHomOf N h⟩

end

end Work.Serre

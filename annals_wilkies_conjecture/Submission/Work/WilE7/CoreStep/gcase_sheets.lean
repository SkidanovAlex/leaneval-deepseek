/-
  `Work.WilE7.CoreStep.gcase_sheets`: the G-case sheet package of `CoreLT_succ`.

  Over a preconnected base `C` and a family of pieces `S t` (`Good`, of full `π_n`-rank
  `n + (m+1) - (S t).j`, with finite fibres over `C`, given by their sheet families `s t` which are
  continuous, pointwise injective, inside `absSet (S t)` and covering its fibres over `C`), the
  *closed* levels `lev t j x = (s t j x) (Fin.last m)` of the sheets satisfy

  (1) the fibre bound `|lev t j x| ≤ 1` (`lev` is a coordinate of `absSet (S t) ⊆ cubeC`);
  (2) the trichotomy `lev t j ≡ 1` / `lev t j ≡ -1` / `|lev t j| < 1` on `C`;
  (3) the level dichotomy: if two sheets agree at one point of `C` then they agree on all of `C`.

  Structure of the proof.

  * (3) is `Work.CoreStep.hdich_of_pieces`, whose proof goes through
    `Work.CoreStep.persist_of_Zavoid_cross2` and hence carries that lemma's *global* fibre
    finiteness hypothesis, which is however **never used** in its proof.  We therefore run the
    argument against the finiteness-free variant `Work.CoreStep.persist_cross2_nofin`
    (delegated), giving `hdich_of_pieces_nofin` below with the hypothesis weakened to the local
    one supplied by the caller.
  * (2) is `Work.CoreStep.level_trichotomy` (delegated) applied to each `S t`, with the
    covering hypothesis `hsep` derived from `hsl`: at `σ = ±1`, the slice of `absSet (S t)` over
    `σ` either meets `C` nowhere (then no sheet attains `σ` on `C`) or covers `C` (then every
    `x ∈ C` has *some* sheet attaining `σ` at `x`, and a further application of (3) pins the
    value to the sheet under consideration).
  * (1) is the cube bound `Work.WilE7.CoreStep.absSet_subset_cubeC`.
-/
import Mathlib
import Submission.Work.CoreStep.sheets_over_cell_of_hrank_localFin
import Submission.Work.CoreStep.hdich_of_pieces
import Submission.Work.CoreStep.persist_cross2_nofin
import Submission.Work.CoreStep.level_trichotomy
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.CoreStep.VerticalG
import Submission.Work.CoreStep.level_eq_const_of_cover

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.CoreStep
open Work.WilE7.MainDesign

/-- The base projection of a point of the form `Fin.append x y` is `x`. -/
private theorem projFirst_finAppend {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    WilkiesDesign.E.projFirst n m (Fin.append x y) = x := by
  funext i
  exact Fin.append_left x y i

/-- The fibre projection of a point of the form `Fin.append x y` is `y`. -/
private theorem projSnd_finAppend {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    WilkiesDesign.E.projSnd n m (Fin.append x y) = y := by
  funext i
  exact Fin.append_right x y i

/-- `Work.CoreStep.hdich_of_pieces` with the fibre-finiteness hypothesis removed: the proof of
`Work.CoreStep.persist_of_Zavoid_cross2` never uses it, and the level dichotomy only uses the
persistence around a point of `C`. -/
theorem hdich_of_pieces_nofin {n m r : ℕ} (k : Fin r → ℕ)
    (T : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : ∀ t : Fin r, (T t).Good)
    (hrank : ∀ (t : Fin r) (z : Fin (0 + (n + (m + 1))) → ℝ), z ∈ (T t).X.set →
      Work.WilE7.MainDesign.projRank (T t) z = n + (m + 1) - (T t).j)
    (C : Set (Fin n → ℝ)) (hpre : IsPreconnected C)
    (s : ∀ t : Fin r, Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hinj : ∀ (t : Fin r) (x : Fin n → ℝ), x ∈ C →
      Function.Injective fun j : Fin (k t) => s t j x)
    (hsub : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (s t j x)) ∈ (T t).X.set)
    (hcov : ∀ (t : Fin r) (z : Fin (n + (m + 1)) → ℝ),
      z ∈ Work.WilE7.MainDesign.absSet (T t) →
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin (k t), s t j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (Wl : Fin r → Fin r → List (WilkiesDesign.E.Stratum 0 (pPair n m)))
    (hWlgood : ∀ (i j : Fin r) (W : WilkiesDesign.E.Stratum 0 (pPair n m)),
      W ∈ Wl i j → W.Good)
    (hWlsub : ∀ (i j : Fin r) (W : WilkiesDesign.E.Stratum 0 (pPair n m)),
      W ∈ Wl i j → W.X.set ⊆ (absLevelPairSet (T i) (T j)).set)
    (hWlcov : ∀ i j : Fin r,
      (absLevelPairSet (T i) (T j)).set = ⋃ W ∈ Wl i j, W.X.set)
    (havoid : ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s i a x₀) (Fin.last m) = (s j b x₀) (Fin.last m) →
      (∀ W ∈ Wl i j, pPair n m - W.j < n + (m + 1) - (T i).j →
        pairPtUp
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s i a x₀)))
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s j b x₀))) ∉ W.X.set) ∧
      (∀ W ∈ Wl i j, pPair n m - W.j = n + (m + 1) - (T i).j →
        pairPtUp
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s i a x₀)))
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s j b x₀))) ∉
            closure W.X.set \ W.X.set)) :
    ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)),
      (∃ x ∈ C, (s i a x) (Fin.last m) = (s j b x) (Fin.last m)) →
      ∀ x ∈ C, (s i a x) (Fin.last m) = (s j b x) (Fin.last m) := by
  -- Step 1: pairwise persistence of the level identity, assembled from the piece data.
  have hpers : ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s i a x₀) (Fin.last m) = (s j b x₀) (Fin.last m) →
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U,
        (s i a x) (Fin.last m) = (s j b x) (Fin.last m) := by
    intro i j a b x₀ hx₀ hlev
    exact Work.CoreStep.persist_cross2_nofin (T i) (T j) (hT i) (hT j)
      (hrank i) (hrank j) C (s i) (s j)
      (hcont i) (hcont j) (hinj i) (hinj j) (hsub i) (hsub j) (hcov i) (hcov j)
      (Wl i j) (hWlgood i j) (hWlsub i j) (hWlcov i j)
      (fun a' b' x' hx' hlev' => havoid i j a' b' x' hx' hlev') a b x₀ hx₀ hlev
  -- Step 2: the clopen argument on the preconnected base `C`.
  intro i j a b hex x hx
  classical
  let φ : C → ℝ := fun y => (s i a (y : Fin n → ℝ)) (Fin.last m)
  let ψ : C → ℝ := fun y => (s j b (y : Fin n → ℝ)) (Fin.last m)
  let A : Set C := {y | φ y = ψ y}
  have hφcont : Continuous φ :=
    (continuous_apply (Fin.last m)).comp
      ((hcont i a).comp_continuous continuous_subtype_val (fun y => y.2))
  have hψcont : Continuous ψ :=
    (continuous_apply (Fin.last m)).comp
      ((hcont j b).comp_continuous continuous_subtype_val (fun y => y.2))
  -- closed: preimage of the diagonal under a continuous map
  have hAclosed : IsClosed A := isClosed_eq hφcont hψcont
  -- nonempty: the given point of `C` where the two sheets agree
  have hAne : A.Nonempty := by
    obtain ⟨x₀, hx₀C, hx₀eq⟩ := hex
    exact ⟨⟨x₀, hx₀C⟩, by simpa [A, φ, ψ] using hx₀eq⟩
  -- open: persistence of the identity gives a neighbourhood of every point of `A`
  have hloc : ∀ y : C, y ∈ A → ∃ V : Set (Fin n → ℝ), IsOpen V ∧ (y : Fin n → ℝ) ∈ V ∧
      ∀ z : C, (z : Fin n → ℝ) ∈ V → z ∈ A := by
    intro y hy
    obtain ⟨U, hU, hUU⟩ :=
      hpers i j a b (y : Fin n → ℝ) y.2 (by simpa [A, φ, ψ] using hy)
    obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
    refine ⟨V, hVopen, hyV, ?_⟩
    intro z hz
    have hz' : (s i a (z : Fin n → ℝ)) (Fin.last m)
        = (s j b (z : Fin n → ℝ)) (Fin.last m) :=
      hUU (z : Fin n → ℝ) ⟨z.2, hVU hz⟩
    simpa [A, φ, ψ] using hz'
  choose V hVopen hyV hVgood using hloc
  let W : Set (Fin n → ℝ) := ⋃ y, ⋃ (hy : y ∈ A), V y hy
  have hWopen : IsOpen W := isOpen_iUnion fun y => isOpen_iUnion fun hy => hVopen y hy
  have hAeq : A = Subtype.val ⁻¹' W := by
    ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hyV z hz⟩⟩
    · intro hz
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hyA, hzy⟩ := Set.mem_iUnion.mp hy
      exact hVgood y hyA z hzy
  have hAopen : IsOpen A := hAeq ▸ hWopen.preimage continuous_subtype_val
  -- `C` is preconnected, so its only clopen subsets are `∅` and `univ`
  have hunivpre : IsPreconnected (Set.univ : Set C) :=
    (Subtype.preconnectedSpace hpre).isPreconnected_univ
  rcases hunivpre.subset_or_subset hAopen hAclosed.isOpen_compl disjoint_compl_right
      (fun z _ => _root_.by_cases (fun hz : z ∈ A => Or.inl hz) (fun hz => Or.inr hz))
      with hsub' | hsub'
  · exact hsub' (Set.mem_univ ⟨x, hx⟩)
  · exact absurd hAne.some_mem (hsub' (Set.mem_univ hAne.some))

theorem gcase_sheets {n m r : ℕ}
    (S : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (hCpre : IsPreconnected C)
    (hGood : ∀ t : Fin r, (S t).Good)
    (hrank : ∀ t : Fin r, ∀ z ∈ (S t).X.set,
      Work.WilE7.MainDesign.projRank (S t) z = n + (m + 1) - (S t).j)
    (hfin : ∀ t : Fin r, ∀ x ∈ C,
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet (S t)) x).Finite)
    (k : Fin r → ℕ) (hk : ∀ t, 0 < k t)
    (s : ∀ t : Fin r, Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hinj : ∀ (t : Fin r) (x : Fin n → ℝ), x ∈ C →
      Function.Injective fun j : Fin (k t) => s t j x)
    (hsub : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C,
      Fin.append x (s t j x) ∈ Work.WilE7.MainDesign.absSet (S t))
    (hcov : ∀ (t : Fin r), ∀ z ∈ Work.WilE7.MainDesign.absSet (S t),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
        ∃ j : Fin (k t), s t j (WilkiesDesign.E.projFirst n (m + 1) z) =
          WilkiesDesign.E.projSnd n (m + 1) z)
    (hsl : ∀ (t : Fin r) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      (C ∩ WilkiesDesign.E.projFirst n (m + 1) ''
          {z | z ∈ Work.WilE7.MainDesign.absSet (S t) ∧
            Work.WilE7.CoreStep.vertCoord (WilkiesDesign.E.projSnd n (m + 1) z) = σ} = ∅) ∨
      (C ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
          {z | z ∈ Work.WilE7.MainDesign.absSet (S t) ∧
            Work.WilE7.CoreStep.vertCoord (WilkiesDesign.E.projSnd n (m + 1) z) = σ}))
    (Wl : Fin r → Fin r → List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlGood : ∀ (i j : Fin r), ∀ W ∈ Wl i j, W.Good)
    (hWlsub : ∀ (i j : Fin r), ∀ W ∈ Wl i j,
      W.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet (S i) (S j)).set)
    (hWlcov : ∀ (i j : Fin r),
      (Work.WilE7.CoreStep.absLevelPairSet (S i) (S j)).set = ⋃ W ∈ Wl i j, W.X.set)
    (havoid : ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s i a x₀) (Fin.last m) = (s j b x₀) (Fin.last m) →
        (∀ W ∈ Wl i j, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - (S i).j →
          Work.WilE7.CoreStep.pairPtUp
            (Work.WilE7.CoreStep.absPtUp (Fin.append x₀ (s i a x₀)))
            (Work.WilE7.CoreStep.absPtUp (Fin.append x₀ (s j b x₀))) ∉ W.X.set) ∧
        (∀ W ∈ Wl i j, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - (S i).j →
          Work.WilE7.CoreStep.pairPtUp
            (Work.WilE7.CoreStep.absPtUp (Fin.append x₀ (s i a x₀)))
            (Work.WilE7.CoreStep.absPtUp (Fin.append x₀ (s j b x₀))) ∉
              closure W.X.set \ W.X.set)) :
    (∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, |(s t j x) (Fin.last m)| ≤ 1) ∧
    (∀ (t : Fin r) (j : Fin (k t)),
      (∀ x ∈ C, (s t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ C, (s t j x) (Fin.last m) = -1) ∨
      (∀ x ∈ C, |(s t j x) (Fin.last m)| < 1)) ∧
    (∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
      ∀ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) := by
  -- The sheets lie in `absSet (S t)`, in the `absPtUp` bookkeeping expected by the pair data.
  have hsubU : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ C →
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s t j x)) ∈ (S t).X.set := by
    intro t j x hx
    exact (Work.CoreStep.mem_absSet_iff (S t) (Fin.append x (s t j x))).mp (hsub t j x hx)
  -- (3) the level dichotomy.
  have hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
      ∀ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m) :=
    hdich_of_pieces_nofin k S hGood hrank C hCpre s hcont hinj hsubU hcov Wl
      hWlGood hWlsub hWlcov havoid
  -- (1) the fibre bound.
  have hbnd : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, |(s t j x) (Fin.last m)| ≤ 1 := by
    intro t j x hx
    have hc := absSet_subset_cubeC (S t) (hsub t j x hx)
    have hlast := hc (Fin.natAdd n (Fin.last m))
    rwa [Fin.append_right] at hlast
  -- The `±1` covering alternatives extracted from `hsl`.
  have hsep : ∀ (t : Fin r) (j : Fin (k t)) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      (∀ x ∈ C, (s t j x) (Fin.last m) ≠ σ) ∨
      (∀ x ∈ C, ∃ j' : Fin (k t), (s t j' x) (Fin.last m) = σ) := by
    intro t j σ hσ
    rcases hsl t σ hσ with hdisj | hcov'
    · -- the `σ`-slice misses `C` altogether: no sheet attains `σ` there
      left
      intro x hx hxσ
      have hmem : x ∈ C ∩ WilkiesDesign.E.projFirst n (m + 1) ''
          {z | z ∈ Work.WilE7.MainDesign.absSet (S t) ∧
            Work.WilE7.CoreStep.vertCoord (WilkiesDesign.E.projSnd n (m + 1) z) = σ} := by
        refine ⟨hx, ⟨Fin.append x (s t j x), ⟨hsub t j x hx, ?_⟩, ?_⟩⟩
        · rw [projSnd_finAppend]
          exact hxσ
        · exact projFirst_finAppend x (s t j x)
      rw [hdisj] at hmem
      exact hmem
    · -- the `σ`-slice surjects onto `C`: every point of `C` is hit by some sheet
      right
      intro x hx
      obtain ⟨z, ⟨hzA, hzσ⟩, hzx⟩ := hcov' hx
      obtain ⟨j', hj'⟩ := hcov t z hzA (hzx.symm ▸ hx)
      refine ⟨j', ?_⟩
      have h1 : (s t j' (WilkiesDesign.E.projFirst n (m + 1) z)) (Fin.last m) = σ := by
        rw [hj']
        exact hzσ
      rw [← hzx]
      exact h1
  -- (2) the trichotomy, from the abstract `level_trichotomy`.
  have htri : ∀ (t : Fin r) (j : Fin (k t)),
      (∀ x ∈ C, (s t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ C, (s t j x) (Fin.last m) = -1) ∨
      (∀ x ∈ C, |(s t j x) (Fin.last m)| < 1) := by
    intro t j
    exact Work.CoreStep.level_trichotomy (s t) (hk t) hCpre (hcont t)
      (fun j j' h => hdich t t j j' h) (hbnd t) (hsep t) j
  exact ⟨hbnd, htri, hdich⟩

end Work.WilE7.CoreStep

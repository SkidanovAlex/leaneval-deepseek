/-
  WilG4c / `AlSliceBase` — the vocabulary for the proof that the *fibre* (slice) derivative
  graph `AlDgListSlice` is `Ω`-definable with format uniform in the order `|L|` and degree
  polynomial in `D, |L|`.

  ## The objects

  `p` parameters, `n + 1` cube coordinates, `F := famFunHat f : ℝ^{p + (n+1)} → ℝ` the family
  member read as a single function (its graph is `famGraph f`).

  * `jLoc p n f k` — `U_k`, the interior of the joint `C^k`-locus of `F` (open).  The only
    smoothness source is `SOMin.SharpDeriv`, which produces the graph of the `k`-th joint
    derivative *over* `U_k`.
  * `jBad p n f k` — `V_k = U_kᶜ` (closed, empty interior).
  * `dgSet p n f m v` — the graph of the joint `m`-th directional derivative of `F` along the
    word `v` of *cube* directions, over `U_m`; verbatim the set `SOMin.SharpDeriv` exhibits.
  * `ProjLim p n A` — the `(p + (n+1))`-dimensional set of points `w` for which the `A`-values
    along the punctured cube tend to some real (existentially quantified).
  * `AlBad p n f L`, `AlGood p n f L` — the "degenerate" region of the target and its
    complement.  `z = (l,u,s) ∈ AlBad` iff for some `k ≤ |L|` a whole fibre ball (of cube
    points, with the parameter fixed at `l`) is contained in `V_k`.  On `AlGood` therefore the
    fibre-good set is *dense* in every fibre ball (`AlGood_dense`): the fibre of `V_k` over `l`
    has empty interior — but it can be a thin hypersurface, so one cannot conclude that the
    whole punctured fibre lies in `U_k`.  Closing that gap is the content of the "tame
    puncture-filling" step of the proof.
  * `Crit p n f L` — the punctured-limit criterion.  It consists of
      (C0) the value condition `Fin.init z ∈ contSet`: the `F`-values along the punctured cube
           tend to `F (Fin.init z)` (fibre continuity);
      (C1) for every order `m ∈ {1,…,k}` and every "counts" vector `c : Fin (n+1) → Fin (m+1)`,
           the values of the joint `m`-th derivative of `F` along the word `cntWord n m c`
           (the word whose letters have the prescribed multiplicities) tend to some real along
           the punctured cube;
      (C2) the values of the joint `k`-th derivative along the word `L` tend to `z`'s last
           coordinate.

  `Crit` is the set the `Ω`-machine can produce (`CritMem`): the index set of (C1) is the sigma
  of `Fin (n+1) → Fin (m+1)` over `m < k`, of cardinality `Σ_{m<k}(m+1)^{n+1} ≤ k^{n+2}`,
  polynomial in `k`.

  ## The mathematics of `Crit`

  `iteratedFDeriv` is symmetric under permutations of the word (`IteratedFDerivPerm`), so the
  conditions (C1) for *all* counts vectors cover, up to permutation, every word: for a word `v`
  put `c := wordCounts v`; then `cntWord n m c` is a permutation of `v`.  Consequently (C1) says
  precisely that every iterated derivative of the fibre has a limit along the punctured cube,
  which `ContDiffAtOfTendstoIteratedFDeriv` (proved) turns into `ContDiffAt ℝ k (fibre) u` once
  the punctured fibre is known to be `C^k` off a thin set; (C2) then identifies `z`'s last
  coordinate with the fibre's `k`-th derivative along `L`.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.FibreLimitPiOmega

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The fibre point -/

/-- The point `(l, y)` of `ℝ^{p + (n+1)}`: the parameter of `w` and the cube point `y`.  The fibre
of `w = (l,u)` is the set of `fibPt w y` with `y` running over the cube points. -/
def fibPt {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) (y : Fin (n + 1) → ℝ) :
    Fin (p + (n + 1)) → ℝ :=
  Fin.append (parPt w) y

@[simp] theorem fibPt_cubePt {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) :
    fibPt w (cubePt w) = w := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [fibPt, Fin.append_left, parPt_apply]
  · simp only [fibPt, Fin.append_right, cubePt_apply]

/-- The distance of two fibre points is the distance of their cube points (both metrics are the
sup metric). -/
theorem dist_fibPt {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) (y y' : Fin (n + 1) → ℝ) :
    dist (fibPt w y') (fibPt w y) = dist y' y := by
  refine le_antisymm ?_ ?_
  · rw [dist_pi_le_iff (show (0 : ℝ) ≤ dist y' y from dist_nonneg)]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [fibPt, Fin.append_left]
      simp
    · simpa only [fibPt, Fin.append_right] using
        (dist_pi_le_iff (show (0 : ℝ) ≤ dist y' y from dist_nonneg)).mp le_rfl i
  · rw [dist_pi_le_iff (show (0 : ℝ) ≤ dist (fibPt w y') (fibPt w y) from dist_nonneg)]
    intro i
    have h := (dist_pi_le_iff (show (0 : ℝ) ≤ dist (fibPt w y') (fibPt w y)
      from dist_nonneg)).mp le_rfl (Fin.natAdd p i)
    simpa only [fibPt, Fin.append_right] using h

/-! ## 2. The joint smoothness loci -/

/-- `U_k`: the interior of the joint `C^k`-locus of the family member read as a single function.
This is the domain of the set that `SOMin.SharpDeriv` makes `Ω`-definable. -/
def jLoc (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  interior {w : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ k (famFunHat f) w}

/-- `V_k = U_kᶜ`, the joint bad locus. -/
def jBad (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  (jLoc p n f k)ᶜ

/-- The graph of the joint `m`-th directional derivative of `F = famFunHat f` along the word
`v` of cube directions (lifted to `Fin (p + (n+1))` by `Fin.natAdd p`), over `U_m`.  This is
verbatim the set produced by `SOMin.SharpDeriv`. -/
def dgSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (m : ℕ)
    (v : Fin m → Fin (n + 1)) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | Fin.init z ∈ jLoc p n f m ∧
    z (Fin.last (p + (n + 1))) =
      iteratedFDeriv ℝ m (famFunHat f) (Fin.init z)
        (fun i => Pi.single (Fin.natAdd p (v i)) 1)}

/-! ## 3. The punctured-limit set -/

/-- For `A ⊆ ℝ^{p + (n+1) + 1}`, the set of `w : ℝ^{p + (n+1)}` such that the `A`-values along
the punctured cube over the parameter of `w` tend to some real number as the cube point tends to
`cubePt w`.  It is the projection (away from the value coordinate) of `LimeqP p n A`. -/
def ProjLim (p n : ℕ) (A : Set (Fin (p + (n + 1) + 1) → ℝ)) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  projLast (Work.WilG4c.LimeqP p n A)

/-- The "value" condition: the `F`-values along the punctured cube tend to `F` at the punctured
point itself, i.e. the fibre is continuous at the cube point. -/
def contSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  projLast (Work.WilG4c.LimeqP p n (famGraph f) ∩ famGraph f)

/-! ## 4. Words and counts -/

/-- The "counts" of a word: how many times each letter occurs. -/
def wordCounts {n m : ℕ} (v : Fin m → Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun i => (Finset.univ.filter (fun j : Fin m => v j = i)).card

/-- The word of length `m` whose `j`-th letter is the number of `i` with
`c 0 + c 1 + … + c i ≤ j`, capped at `n`.  When `∑ c i = m` this is the nondecreasing word whose
letter `i` occurs `c i` times; for arbitrary `c` it is some word, and the extra conditions it
produces in `Crit` are harmless because *all* word values converge when the fibre is `C^k`. -/
def cntWord (n m : ℕ) (c : Fin (n + 1) → ℕ) (j : Fin m) : Fin (n + 1) :=
  ⟨min ((Finset.univ.filter (fun i : Fin (n + 1) =>
      (∑ k ∈ Finset.univ.filter (fun k => k ≤ i), c k) ≤ j.val)).card) n, by omega⟩

/-! ## 5. The criterion -/

/-- The `m`-th order limit condition for the counts vector `c`: the values of the joint `m`-th
derivative of `F` along the word `cntWord n m c` tend to some real along the punctured cube. -/
def LimCond (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (m : ℕ)
    (c : Fin (n + 1) → ℕ) : Set (Fin (p + (n + 1)) → ℝ) :=
  ProjLim p n (dgSet p n f m (cntWord n m c))

/-- The index set of the conditions (C1) of `Crit`: the orders `1, …, k` together with the
counts vectors `Fin (n+1) → Fin (m+1)`. -/
def critIdx (n k : ℕ) : Finset (Σ m : Fin k, Fin (n + 1) → Fin (m.val + 1)) :=
  Finset.sigma Finset.univ (fun _ => Finset.univ)

/-- **The value-free criterion at a single point.**  A point `w = (l,u)` of `ℝ^{p + (n+1)}`
satisfies it iff the `F`-values along the punctured cube tend to `F w` and, for every order
`m ∈ {1,…,k}` and every counts vector, the corresponding joint word values have a limit at the
punctured cube. -/
def UV (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  contSet p n f ∩ ⋂ i ∈ critIdx n k, LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val)

/-- **The localised punctured-limit criterion.**  `z` satisfies it iff there is a fibre ball
around `z`'s cube point (same parameter) at every point of which the value-free criterion `UV`
holds.  Localising in this way is what makes the criterion *sufficient*: with the criterion
holding at every point of the fibre ball, the standard mean-value argument (splitting segments
at the thin bad set) produces `C^k`-ness of the fibre on the whole ball, not merely
differentiability at the centre. -/
def LocCrit (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | ∃ ρ : ℝ, 0 < ρ ∧ ∀ w' : Fin (p + (n + 1)) → ℝ,
    parPt w' = parPt (Fin.init z) →
      dist (cubePt w') (cubePt (Fin.init z)) < ρ → w' ∈ UV p n f L.length}

/-- **The punctured-limit criterion.**  See the module docstring: the localised criterion
`LocCrit` together with the condition that the joint `|L|`-th derivative along the word `L`
tends to `z`'s last coordinate. -/
def Crit (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  LocCrit p n f L ∩ {z | z ∈ Work.WilG4c.LimeqP p n
    (dgSet p n f L.length (fun j => L.get j))}

/-! ## 6. The degenerate region -/

/-- For a fixed order `k`, the set of `z` such that some fibre ball is contained in `V_k`. -/
def AlBadK (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
    ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε → fibPt (Fin.init z) y ∈ jBad p n f k}

/-- **The degenerate region.** `z ∈ AlBad p n f L` iff for some `k ≤ |L|` a whole fibre ball of
`z` consists of points outside the joint `C^k`-locus.  Its parameter projection is thin
(`AlBadParThin`), which is what lets the recursion on the number of parameters handle it. -/
def AlBad (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  ⋃ k : Fin (L.length + 1), AlBadK p n f k

/-- The complement of `AlBad`. -/
def AlGood (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  (AlBad p n f L)ᶜ

/-- The projection of `AlBad` to the parameter coordinates. -/
def AlBadPar (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin p → ℝ) :=
  {l | ∃ (u : Fin (n + 1) → ℝ) (s : ℝ),
    Fin.snoc (Fin.append l u) s ∈ AlBad p n f L}

/-- The projection of `AlBadK` to the parameter coordinates. -/
def AlBadKPar (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin p → ℝ) :=
  {l | ∃ (u : Fin (n + 1) → ℝ) (s : ℝ),
    Fin.snoc (Fin.append l u) s ∈ AlBadK p n f k}

/-! ## 7. Unfoldings -/

@[simp] theorem mem_dgSet {p n m : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (v : Fin m → Fin (n + 1))
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    z ∈ dgSet p n f m v ↔
      Fin.init z ∈ jLoc p n f m ∧
      z (Fin.last (p + (n + 1))) =
        iteratedFDeriv ℝ m (famFunHat f) (Fin.init z)
          (fun i => Pi.single (Fin.natAdd p (v i)) 1) :=
  Iff.rfl

@[simp] theorem mem_AlBadK {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ)
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    z ∈ AlBadK p n f k ↔
      ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
        ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε → fibPt (Fin.init z) y ∈ jBad p n f k :=
  Iff.rfl

theorem mem_AlGood {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) (z : Fin (p + (n + 1) + 1) → ℝ) :
    z ∈ AlGood p n f L ↔ z ∉ AlBad p n f L :=
  Iff.rfl

/-- **On `AlGood` the fibre-good set is dense in every fibre ball.**  For every order `k ≤ |L|`,
every cube point `y₀` and every `ε > 0` there is `y` with `dist y y₀ < ε` and
`(l, y) ∈ U_k` (`l` the parameter of `z`).  Equivalently: the fibre of `V_k` over `l` has empty
interior. -/
theorem AlGood_dense {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    {z : Fin (p + (n + 1) + 1) → ℝ} (hz : z ∈ AlGood p n f L)
    {k : ℕ} (hk : k ≤ L.length) (y₀ : Fin (n + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Fin (n + 1) → ℝ, dist y y₀ < ε ∧ fibPt (Fin.init z) y ∈ jLoc p n f k := by
  by_contra hcon
  apply hz
  refine Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_⟩
  refine ⟨y₀, ε, hε, ?_⟩
  intro y hy
  exact fun hyU => hcon ⟨y, hy, hyU⟩

/-! ## 8. The coordinate map of a thin-cell parametrisation -/

/-- `cutIdxHat p p' n e` maps the coordinates of the `p'`-parameter space (parameters first, then
the `n+1` cube coordinates, then the value coordinate) into the coordinates of the `p`-parameter
space, sending the parameter coordinate `i` to `e i` and fixing the cube and value
coordinates. -/
def cutIdxHat (p p' n : ℕ) (e : Fin p' ↪ Fin p) :
    Fin (p' + (n + 1) + 1) → Fin (p + (n + 1) + 1) :=
  fun j => if h : (j : ℕ) < p' then ⟨(e ⟨j, h⟩).val, by have := (e ⟨j, h⟩).isLt; omega⟩
    else ⟨p + ((j : ℕ) - p'), by have := j.isLt; omega⟩

/-- The cube coordinates are untouched by `cutIdxHat`. -/
theorem cubePt_cutIdxHat {p p' n : ℕ} (e : Fin p' ↪ Fin p)
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    cubePt (Fin.init (z ∘ cutIdxHat p p' n e)) = cubePt (Fin.init z) := by
  funext j
  have hlt : ¬ ((Fin.castSucc (Fin.natAdd p' j) : Fin (p' + (n + 1) + 1)) : ℕ) < p' := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]; omega
  have hidx : cutIdxHat p p' n e (Fin.castSucc (Fin.natAdd p' j))
      = Fin.castSucc (Fin.natAdd p j) := by
    rw [cutIdxHat, dif_neg hlt]
    refine Fin.ext ?_
    simp only [Fin.val_castSucc, Fin.val_natAdd]
    omega
  show z (cutIdxHat p p' n e (Fin.castSucc (Fin.natAdd p' j))) = z (Fin.castSucc (Fin.natAdd p j))
  rw [hidx]

/-- The parameter coordinates of `z ∘ cutIdxHat` are the `e`-selected parameter coordinates. -/
theorem parPt_cutIdxHat {p p' n : ℕ} (e : Fin p' ↪ Fin p)
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    parPt (Fin.init (z ∘ cutIdxHat p p' n e)) = fun i : Fin p' => parPt (Fin.init z) (e i) := by
  funext i
  have hlt : ((Fin.castSucc (Fin.castAdd (n + 1) i) : Fin (p' + (n + 1) + 1)) : ℕ) < p' := by
    simp only [Fin.val_castSucc, Fin.val_castAdd]; exact i.isLt
  have hidx : cutIdxHat p p' n e (Fin.castSucc (Fin.castAdd (n + 1) i))
      = Fin.castSucc (Fin.castAdd (n + 1) (e i)) := by
    rw [cutIdxHat, dif_pos hlt]
    exact Fin.ext rfl
  show z (cutIdxHat p p' n e (Fin.castSucc (Fin.castAdd (n + 1) i)))
      = z (Fin.castSucc (Fin.castAdd (n + 1) (e i)))
  rw [hidx]

/-- The value coordinate is untouched by `cutIdxHat`. -/
theorem last_cutIdxHat {p p' n : ℕ} (e : Fin p' ↪ Fin p)
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    (z ∘ cutIdxHat p p' n e) (Fin.last (p' + (n + 1))) = z (Fin.last (p + (n + 1))) := by
  have hlt : ¬ ((Fin.last (p' + (n + 1)) : Fin (p' + (n + 1) + 1)) : ℕ) < p' := by
    simp only [Fin.val_last]; omega
  have hidx : cutIdxHat p p' n e (Fin.last (p' + (n + 1))) = Fin.last (p + (n + 1)) := by
    rw [cutIdxHat, dif_neg hlt]
    refine Fin.ext ?_
    simp only [Fin.val_last]
    omega
  show z (cutIdxHat p p' n e (Fin.last (p' + (n + 1)))) = z (Fin.last (p + (n + 1)))
  rw [hidx]

end Work.WilkG4c

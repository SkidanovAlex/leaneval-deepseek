/-
  The target lemma of the `WilG4c` area: the near-maximality of the chosen curves `γs` for
  *every* direction list, rather than only for the fixed "pure" lists.

  `hmax_of_choice_lists` is the statement that the choice curves `γs L` (one for each direction
  list `L` of length `≤ r`, chosen so that `γs L x` is a `2`-approximate maximiser of
  `|∂^L f_l|` over the fibre at `x` whenever such a maximiser exists) satisfy the near-maximality
  inequality for the direction list `0^j` followed by the `y`-directions of `M`, evaluated at the
  point `y` on the one hand and along the curve `γs Lc` on the other, where `Lc` is the
  "count vector" listing of the multiset of `M`.

  The two ingredients are:
  * the boundedness hypothesis `hBdd` (off the exceptional set `B`), which supplies a
    `2`-approximate maximiser and hence fires the implication `hchoice` at the list `Lc`;
  * the identification of `iterDir` along the list `Ldir = 0^j ++ M.map Fin.succ` with the
    iterated Fréchet derivative along the permuted list `Lc = 0^j ++ (countvector M).map Fin.succ`
    (mixed partial derivatives commute).

  The auxiliary lemmas used here live in `Submission/Work/WilG4c/HmaxAux.lean` (a fresh module of
  the same area), which also records why they are restated rather than imported from their
  original modules.
-/
import Mathlib
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.HmaxAux

namespace Work.WilkG4c

theorem hmax_of_choice_lists {n p r : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (B : Finset ℝ)
    (γs : (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ))
    (hchoice : ∀ (L : List (Fin (n + 1))), L.length ≤ r →
      (∀ x : ℝ,
        (∃ y : Fin n → ℝ, y ∈ WilkiesDesign.openCube n ∧
            ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
              (Work.WilkG4c.pt x y) ∧
            ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
              ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                (Work.WilkG4c.pt x y') →
              |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                  (Work.WilkG4c.pt x y') (fun j => Pi.single (L.get j) 1)| ≤
                2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                  (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|) →
          γs L x ∈ WilkiesDesign.openCube n ∧
          ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
            (Work.WilkG4c.pt x (γs L x)) ∧
          ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
            ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
              (Work.WilkG4c.pt x y') →
            |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                (Work.WilkG4c.pt x y') (fun j => Pi.single (L.get j) 1)| ≤
              2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                (Work.WilkG4c.pt x (γs L x)) (fun j => Pi.single (L.get j) 1)|))
    (hBdd : ∀ (L : List (Fin (n + 1))), L.length ≤ r →
      ∀ x ∈ Work.WilkG4c.I, x ∉ (B : Set ℝ) →
        BddAbove ((fun y : Fin n → ℝ =>
            |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
              (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|) ''
          {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
            ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
              (Work.WilkG4c.pt x y)})) :
    ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ (j + M.length) (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y) →
      |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
          (fun u : Fin (n + 1) → ℝ => f l u) (Work.WilkG4c.pt x y)| ≤
        2 * |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
          (fun u : Fin (n + 1) → ℝ => f l u)
          (Work.WilkG4c.curveFun
            (γs (List.replicate j (0 : Fin (n + 1)) ++
              ((Finset.univ.sum (fun i : Fin n => (Multiset.ofList M).count i •
                ({i} : Multiset (Fin n)))).toList.map Fin.succ))) x)| := by
  intro j M x y hjr hxI hxB hy hcd
  -- Abbreviations: `cv` is the "count vector" listing of the multiset of `M`, `Lc` the
  -- direction list it indexes (the one on which the curves `γs` are keyed), and `Ldir` the
  -- direction list appearing in the conclusion.
  let cv : List (Fin n) := (Finset.univ.sum (fun i : Fin n =>
    (Multiset.ofList M).count i • ({i} : Multiset (Fin n)))).toList
  let Lc : List (Fin (n + 1)) := List.replicate j (0 : Fin (n + 1)) ++ cv.map Fin.succ
  let Ldir : List (Fin (n + 1)) := List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ
  change |Work.WilkG4c.iterDir Ldir (fun u : Fin (n + 1) → ℝ => f l u) (Work.WilkG4c.pt x y)| ≤
    2 * |Work.WilkG4c.iterDir Ldir (fun u : Fin (n + 1) → ℝ => f l u)
      (Work.WilkG4c.curveFun (γs Lc) x)|
  have hMlen : M.length ≤ r := by omega
  -- `Ldir` and `Lc` differ only by the order of the `y`-directions: the count vector of `M`
  -- is a permutation of `M`.
  have hperm : Ldir.Perm Lc := by
    have hLdir : Ldir = List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ := rfl
    have hLc : Lc = List.replicate j (0 : Fin (n + 1)) ++ cv.map Fin.succ := rfl
    rw [hLdir, hLc]
    exact List.Perm.append_left _ ((hmax_countvec_perm M hMlen).map Fin.succ)
  have hlen : Lc.length = j + M.length := by
    have hLc : Lc = List.replicate j (0 : Fin (n + 1)) ++ cv.map Fin.succ := rfl
    have hcvlen : cv.length = M.length := ((hmax_countvec_perm M hMlen).length_eq).symm
    rw [hLc]
    simp only [List.length_append, List.length_replicate, List.length_map, hcvlen]
  have hlenle : Lc.length ≤ r := by rw [hlen]; exact hjr
  have hcdLc : ContDiffAt ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
      (Work.WilkG4c.pt x y) := by rw [hlen]; exact hcd
  -- The boundedness hypothesis, transported to the direction list `Lc`.
  have hbddLc : BddAbove ((fun y' : Fin n → ℝ =>
      |iteratedFDeriv ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y') (fun k => Pi.single (Lc.get k) 1)|) ''
      {y' : Fin n → ℝ | y' ∈ WilkiesDesign.openCube n ∧
        ContDiffAt ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
          (Work.WilkG4c.pt x y')}) :=
    hBdd Lc hlenle x hxI hxB
  -- The fibre locus at `x` is inhabited (by `y`), so the boundedness produces a
  -- `2`-approximate maximiser of `|∂^{Lc}|`.
  have hne : ({y' : Fin n → ℝ | y' ∈ WilkiesDesign.openCube n ∧
      ContDiffAt ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y')}).Nonempty :=
    ⟨y, hy, by rw [hlen]; exact hcd⟩
  obtain ⟨y₀, hy₀, hy₀max⟩ := hmax_nearmax_of_bdd hne
    (fun y' => iteratedFDeriv ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
      (Work.WilkG4c.pt x y') (fun k => Pi.single (Lc.get k) 1))
    (by simpa using hbddLc)
  -- The choice hypothesis now exhibits `γs Lc x` as a `2`-approximate maximiser as well.
  have hch :=
    hchoice Lc hlenle x ⟨y₀, hy₀.1, hy₀.2, fun y' hy' hcd' => hy₀max y' ⟨hy', hcd'⟩⟩
  obtain ⟨_hγcube, hγcd, hγmax⟩ := hch
  have hyb : |iteratedFDeriv ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y) (fun k => Pi.single (Lc.get k) 1)| ≤
      2 * |iteratedFDeriv ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x (γs Lc x)) (fun k => Pi.single (Lc.get k) 1)| :=
    hγmax y hy (by rw [hlen]; exact hcd)
  -- Smoothness at the two points where `iterDir` is evaluated.
  have hLdir_len : Ldir.length = j + M.length := by
    have hLdir : Ldir = List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ := rfl
    rw [hLdir]
    simp
  have hcdLdir : ContDiffAt ℝ Ldir.length (fun u : Fin (n + 1) → ℝ => f l u)
      (Work.WilkG4c.pt x y) := by rw [hLdir_len]; exact hcd
  have hccLdir : ContDiffAt ℝ Ldir.length (fun u : Fin (n + 1) → ℝ => f l u)
      (Work.WilkG4c.curveFun (γs Lc) x) := by
    rw [hLdir_len]
    have hγcd' : ContDiffAt ℝ (j + M.length) (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x (γs Lc x)) := by simpa [hlen] using hγcd
    simpa [Work.WilkG4c.curveFun] using hγcd'
  -- Convert the iterated directional derivatives into the `iteratedFDeriv` form in which the
  -- near-maximality statement is phrased, using permutation invariance of `iterDir`.
  have eL : Work.WilkG4c.iterDir Ldir (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y) =
      iteratedFDeriv ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y) (fun k => Pi.single (Lc.get k) 1) :=
    (hmax_iterDir_perm (fun u : Fin (n + 1) → ℝ => f l u) hperm
        (Work.WilkG4c.pt x y) hcdLdir).trans
      (hmax_iterDir_eq_iteratedFDeriv Lc (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y) hcdLc)
  have eR : Work.WilkG4c.iterDir Ldir (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.curveFun (γs Lc) x) =
      iteratedFDeriv ℝ Lc.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x (γs Lc x)) (fun k => Pi.single (Lc.get k) 1) :=
    (hmax_iterDir_perm (fun u : Fin (n + 1) → ℝ => f l u) hperm
        (Work.WilkG4c.curveFun (γs Lc) x) hccLdir).trans
      (hmax_iterDir_eq_iteratedFDeriv Lc (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.curveFun (γs Lc) x) hγcd)
  rw [eL, eR]
  exact hyb

end Work.WilkG4c

namespace Work.WilG4c

/-- The lemma `Work.WilkG4c.hmax_of_choice_lists` re-exported under the namespace spelling of
the module path `Submission.Work.WilG4c.hmax_of_choice_lists`, so that it can be referred to as
`Work.WilG4c.hmax_of_choice_lists` as well as `Work.WilkG4c.hmax_of_choice_lists` (the spelling
used by the neighbouring files of this area). -/
abbrev hmax_of_choice_lists := @Work.WilkG4c.hmax_of_choice_lists

end Work.WilG4c

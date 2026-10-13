/-
  WilG4a — the graph of the chart `chart1 f κ` is `Ω`-definable
  (piece 4 of the `n = 1` family lemma, BNZ §5.1).

  ## What is proved

  Given a cell `κ ⊆ ℝ^{p+1}` and a family member `f : ℝ^p × ℝ → ℝ` whose graph, the cell and
  the graphs of the two end-point functions `Aend κ f`, `Bend κ f` are all `Ω`-definable, and
  such that *for fixed `(l,t)` the equation*
  `f(l,y) = Aend κ f l + (Bend κ f l - Aend κ f l) * t` *has at most one solution* `y`,
  the graph of the chart

  `chart1 f κ l t = if ∃ y, (l,y) ∈ κ ∧ f l y = Aend l + (Bend l - Aend l) * t
                     then (that y) else 1/2`

  is `Ω`-definable, with format and degree depending only on `p`, `F0`, `Fκ` and the polynomial
  `bκ` (the degree is `6 * bκ(D) + 2 * D + 21`).

  ## The construction

  Write `z = (l,t,y)` for a point of `ℝ^{p+2}` and let `W` be the set of points with

      `Fin.snoc l y ∈ κ`  and  `f l y = Aend κ f l + (Bend κ f l - Aend κ f l) * t`,

  and let `E ⊆ ℝ^{p+1}` be its projection along `y` (the set of `(l,t)` for which the defining
  equation is solvable).  The uniqueness hypothesis makes the chosen `y` unique, hence

      `graph (chart1 f κ) = W ∪ ({y = 1/2} ∩ π⁻¹(Eᶜ))`,

  `π : ℝ^{p+2} → ℝ^{p+1}` being the projection `(l,t,y) ↦ (l,t)`.

  Both pieces are `Ω`-definable.  On the `Ω`-side `W` is obtained in `ℝ^{p+2+3}` with three
  auxiliary coordinates `u = Aend κ f l`, `v = Bend κ f l`, `w = f l y`, as the projection of

      `S_κ ∩ S_A ∩ S_B ∩ S_f ∩ {w = u + (v - u) * t}`,

  where each `S_·` is a substitution atom (pullback of the corresponding graph along the
  coordinate map which reads `(l, ·)` from the ambient space).  `E` is the projection of `W`,
  so `π⁻¹(Eᶜ)` is a `prod_right` of the complement of a projection, and `{y = 1/2}` is a
  hypersurface of degree one.

  Concretely `a = max (max (Fκ + 2 * (2p + 6) + 1) (F0 + 2 * (2p + 7) + 1)) (p + 5) + 12`
  and `b = 6 * bκ + 2 * X 0 + 21`.
-/
import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG4a.affine_chart_graph_mem
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesDesign

/-! ## 1. The ambient coordinates of `ℝ^{p+5} = ℝ^{p+2} × ℝ^3`

The surviving coordinates are the first `p+2` (the parameters, the variable `t` and the value
`y`), the eliminated ones the last three (`u`, `v`, `w`). -/

/-- Coordinate `p` of `Fin (p+5)`: the variable `t`. -/
def chgT (p : ℕ) : Fin (p+5) := ⟨p, by omega⟩

/-- Coordinate `p+1` of `Fin (p+5)`: the value `y`. -/
def chgY (p : ℕ) : Fin (p+5) := ⟨p+1, by omega⟩

/-- Coordinate `p+2` of `Fin (p+5)`: a copy of `Aend κ f l`. -/
def chgU (p : ℕ) : Fin (p+5) := ⟨p+2, by omega⟩

/-- Coordinate `p+3` of `Fin (p+5)`: a copy of `Bend κ f l`. -/
def chgV (p : ℕ) : Fin (p+5) := ⟨p+3, by omega⟩

/-- Coordinate `p+4` of `Fin (p+5)`: a copy of `f l y`. -/
def chgW (p : ℕ) : Fin (p+5) := ⟨p+4, by omega⟩

/-! ## 2. The four coordinate-reading maps `Fin _ → Fin (p+5)` -/

/-- Reads `(l, y)` from `ℝ^{p+2+3}` as a point of `ℝ^{p+1}`. -/
def chgIotK (p : ℕ) : Fin (p+1) → Fin (p+5) :=
  Fin.lastCases (chgY p) (fun i => Fin.castAdd 5 i)

/-- Reads `(l, u)` from `ℝ^{p+2+3}` as a point of `ℝ^{p+1}`. -/
def chgIotA (p : ℕ) : Fin (p+1) → Fin (p+5) :=
  Fin.lastCases (chgU p) (fun i => Fin.castAdd 5 i)

/-- Reads `(l, v)` from `ℝ^{p+2+3}` as a point of `ℝ^{p+1}`. -/
def chgIotB (p : ℕ) : Fin (p+1) → Fin (p+5) :=
  Fin.lastCases (chgV p) (fun i => Fin.castAdd 5 i)

/-- Reads `(l, y, w)` from `ℝ^{p+2+3}` as a point of `ℝ^{p+2}`. -/
def chgIotF (p : ℕ) : Fin (p+2) → Fin (p+5) :=
  Fin.lastCases (chgW p) (Fin.lastCases (chgY p) (fun i => Fin.castAdd 5 i))

@[simp] theorem chgIotK_last (p : ℕ) : chgIotK p (Fin.last p) = chgY p := by
  simp [chgIotK]

@[simp] theorem chgIotK_castSucc (p : ℕ) (i : Fin p) :
    chgIotK p (Fin.castSucc i) = Fin.castAdd 5 i := by
  simp [chgIotK]

@[simp] theorem chgIotA_last (p : ℕ) : chgIotA p (Fin.last p) = chgU p := by
  simp [chgIotA]

@[simp] theorem chgIotA_castSucc (p : ℕ) (i : Fin p) :
    chgIotA p (Fin.castSucc i) = Fin.castAdd 5 i := by
  simp [chgIotA]

@[simp] theorem chgIotB_last (p : ℕ) : chgIotB p (Fin.last p) = chgV p := by
  simp [chgIotB]

@[simp] theorem chgIotB_castSucc (p : ℕ) (i : Fin p) :
    chgIotB p (Fin.castSucc i) = Fin.castAdd 5 i := by
  simp [chgIotB]

@[simp] theorem chgIotF_last (p : ℕ) : chgIotF p (Fin.last (p+1)) = chgW p := by
  simp [chgIotF]

@[simp] theorem chgIotF_castSucc_last (p : ℕ) :
    chgIotF p (Fin.castSucc (Fin.last p)) = chgY p := by
  simp [chgIotF]

@[simp] theorem chgIotF_castSucc_castSucc (p : ℕ) (i : Fin p) :
    chgIotF p (Fin.castSucc (Fin.castSucc i)) = Fin.castAdd 5 i := by
  simp [chgIotF]

/-! ## 3. The five pieces of `W` -/

/-- The pullback of the cell `κ` along `(l, y)`: `(l,y) ∈ κ`. -/
def chgSκ (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) : Set (Fin (p+5) → ℝ) :=
  {z | z ∘ chgIotK p ∈ κ}

/-- The pullback of the graph of `lo` along `(l, u)`: `u = lo l`. -/
def chgSA (p : ℕ) (lo : (Fin p → ℝ) → ℝ) : Set (Fin (p+5) → ℝ) :=
  {z | z ∘ chgIotA p ∈ graphOf lo}

/-- The pullback of the graph of `hi` along `(l, v)`: `v = hi l`. -/
def chgSB (p : ℕ) (hi : (Fin p → ℝ) → ℝ) : Set (Fin (p+5) → ℝ) :=
  {z | z ∘ chgIotB p ∈ graphOf hi}

/-- The pullback of the graph of `f` along `(l, y, w)`: `w = f l y`. -/
def chgSF (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p+5) → ℝ) :=
  {z | z ∘ chgIotF p ∈ graphFam f}

/-- The affine relation `w = u + (v - u) * t`. -/
def chgSrel (p : ℕ) : Set (Fin (p+5) → ℝ) :=
  {z | z (chgW p) = z (chgU p) + (z (chgV p) - z (chgU p)) * z (chgT p)}

/-! ## 4. Membership in the five pieces -/

theorem chgSnocK (p : ℕ) (z : Fin (p+5) → ℝ) :
    (z ∘ chgIotK p) =
      Fin.snoc (fun i : Fin p => z (Fin.castAdd 5 i)) (z (chgY p)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Function.comp_apply, chgIotK_last, Fin.snoc_last]
  · intro i
    rw [Function.comp_apply, chgIotK_castSucc, Fin.snoc_castSucc]

theorem mem_chgSκ (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (z : Fin (p+5) → ℝ) :
    z ∈ chgSκ p κ ↔
      Fin.snoc (fun i : Fin p => z (Fin.castAdd 5 i)) (z (chgY p)) ∈ κ := by
  simp only [chgSκ, Set.mem_ofPred_eq, chgSnocK]

theorem mem_chgSA (p : ℕ) (lo : (Fin p → ℝ) → ℝ) (z : Fin (p+5) → ℝ) :
    z ∈ chgSA p lo ↔ z (chgU p) = lo (fun i : Fin p => z (Fin.castAdd 5 i)) := by
  have h1 : (z ∘ chgIotA p) (Fin.last p) = z (chgU p) := by
    rw [Function.comp_apply, chgIotA_last]
  have h2 : Fin.init (z ∘ chgIotA p) = (fun i : Fin p => z (Fin.castAdd 5 i)) := by
    funext i
    show (z ∘ chgIotA p) (Fin.castSucc i) = z (Fin.castAdd 5 i)
    rw [Function.comp_apply, chgIotA_castSucc]
  simp only [chgSA, graphOf, Set.mem_ofPred_eq]
  constructor
  · intro h
    rwa [h1, h2] at h
  · intro h
    rwa [← h1, ← h2] at h

theorem mem_chgSB (p : ℕ) (hi : (Fin p → ℝ) → ℝ) (z : Fin (p+5) → ℝ) :
    z ∈ chgSB p hi ↔ z (chgV p) = hi (fun i : Fin p => z (Fin.castAdd 5 i)) := by
  have h1 : (z ∘ chgIotB p) (Fin.last p) = z (chgV p) := by
    rw [Function.comp_apply, chgIotB_last]
  have h2 : Fin.init (z ∘ chgIotB p) = (fun i : Fin p => z (Fin.castAdd 5 i)) := by
    funext i
    show (z ∘ chgIotB p) (Fin.castSucc i) = z (Fin.castAdd 5 i)
    rw [Function.comp_apply, chgIotB_castSucc]
  simp only [chgSB, graphOf, Set.mem_ofPred_eq]
  constructor
  · intro h
    rwa [h1, h2] at h
  · intro h
    rwa [← h1, ← h2] at h

theorem mem_chgSF (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p+5) → ℝ) :
    z ∈ chgSF p f ↔
      z (chgW p) = f (fun i : Fin p => z (Fin.castAdd 5 i)) (z (chgY p)) := by
  have h1 : (z ∘ chgIotF p) (Fin.last (p+1)) = z (chgW p) := by
    rw [Function.comp_apply, chgIotF_last]
  have h2 : (fun i : Fin p => (z ∘ chgIotF p) (Fin.castSucc (Fin.castSucc i))) =
      (fun i : Fin p => z (Fin.castAdd 5 i)) := by
    funext i
    rw [Function.comp_apply, chgIotF_castSucc_castSucc]
  have h3 : (z ∘ chgIotF p) (Fin.castSucc (Fin.last p)) = z (chgY p) := by
    rw [Function.comp_apply, chgIotF_castSucc_last]
  simp only [chgSF, Set.mem_ofPred_eq, mem_graphFam]
  constructor
  · intro h
    rwa [h1, h2, h3] at h
  · intro h
    rwa [← h1, ← h2, ← h3] at h

theorem mem_chgSrel (p : ℕ) (z : Fin (p+5) → ℝ) :
    z ∈ chgSrel p ↔ z (chgW p) = z (chgU p) + (z (chgV p) - z (chgU p)) * z (chgT p) :=
  Iff.rfl

/-! ## 5. `Ω`-membership of the relation set -/

/-- The polynomial `w - u - (v - u) * t` whose zero set is `chgSrel p`. -/
def chgRelPoly (p : ℕ) : MvPolynomial (Fin (p+5)) ℝ :=
  MvPolynomial.X (chgW p) - MvPolynomial.X (chgU p) -
    (MvPolynomial.X (chgV p) - MvPolynomial.X (chgU p)) * MvPolynomial.X (chgT p)

theorem chgRelPoly_set (p : ℕ) :
    {z : Fin (p+5) → ℝ | MvPolynomial.eval z (chgRelPoly p) = 0} = chgSrel p := by
  ext z
  simp only [Set.mem_ofPred_eq, chgSrel]
  rw [show MvPolynomial.eval z (chgRelPoly p) =
      z (chgW p) - z (chgU p) - (z (chgV p) - z (chgU p)) * z (chgT p) from by
    simp [chgRelPoly]]
  constructor <;> intro h <;> linarith

theorem chgX_sub_le (p : ℕ) (i j : Fin (p+5)) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin (p+5)) ℝ).totalDegree ≤ 1 :=
  le_trans (Work.WilG5.td_sub_le _ _)
    (max_le (Work.WilG5.td_X_le i) (Work.WilG5.td_X_le j))

theorem chgRelPoly_totalDegree_le (p : ℕ) : (chgRelPoly p).totalDegree ≤ 2 := by
  have h1 : (MvPolynomial.X (chgW p) - MvPolynomial.X (chgU p) :
      MvPolynomial (Fin (p+5)) ℝ).totalDegree ≤ 1 := chgX_sub_le p _ _
  have h2 : ((MvPolynomial.X (chgV p) - MvPolynomial.X (chgU p)) *
      MvPolynomial.X (chgT p) : MvPolynomial (Fin (p+5)) ℝ).totalDegree ≤ 2 := by
    refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have h3 : (MvPolynomial.X (chgV p) - MvPolynomial.X (chgU p) :
        MvPolynomial (Fin (p+5)) ℝ).totalDegree ≤ 1 := chgX_sub_le p _ _
    have h4 : (MvPolynomial.X (chgT p) : MvPolynomial (Fin (p+5)) ℝ).totalDegree ≤ 1 :=
      Work.WilG5.td_X_le _
    have h5 : (MvPolynomial.X (chgV p) - MvPolynomial.X (chgU p) :
        MvPolynomial (Fin (p+5)) ℝ).totalDegree +
      (MvPolynomial.X (chgT p) : MvPolynomial (Fin (p+5)) ℝ).totalDegree ≤ 1 + 1 :=
      add_le_add h3 h4
    omega
  exact le_trans (Work.WilG5.td_sub_le _ _)
    (max_le (le_trans h1 (by norm_num)) (le_trans h2 (by norm_num)))

theorem chgSrel_mem (S : SOMin) (p : ℕ) : chgSrel p ∈ S.Ω (p+5) 2 (p+5) := by
  have h := S.hyp (p+5) (chgRelPoly p)
  rw [chgRelPoly_set] at h
  exact Work.WilG5.mem_mono h (p+5) 2 le_rfl (chgRelPoly_totalDegree_le p)

/-! ## 6. The sets `W`, `E` and the second piece -/

/-- The `Ω`-witness of `W`, in `ℝ^{p+2+3}`. -/
def chgWfull (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Set (Fin (p+5) → ℝ) :=
  ((chgSκ p κ ∩ chgSA p (Aend κ f)) ∩ chgSB p (Bend κ f)) ∩ (chgSF p f ∩ chgSrel p)

/-- `W`: the points `(l,t,y)` with `(l,y) ∈ κ` and `f l y = Aend l + (Bend l - Aend l) * t`. -/
def chgWset (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Set (Fin (p+2) → ℝ) :=
  {z | Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p+1))) ∈ κ ∧
    f (Fin.init (Fin.init z)) (z (Fin.last (p+1))) =
      Aend κ f (Fin.init (Fin.init z)) +
        (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
          z (Fin.castSucc (Fin.last p))}

/-- `E`, the projection of `W`: the set of `(l,t)` for which the defining equation is solvable. -/
def chgE (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Set (Fin (p+1) → ℝ) :=
  projLast (chgWset p κ f)

/-- The hypersurface `{y = 1/2}`. -/
def chgHalf (p : ℕ) : Set (Fin (p+2) → ℝ) := {z | z (Fin.last (p+1)) = 1/2}

/-- The second piece of the graph of the chart: the junk values. -/
def chgSecond (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Set (Fin (p+2) → ℝ) :=
  chgHalf p ∩ {z | Fin.init z ∈ (chgE p κ f)ᶜ}

theorem mem_chgWfull (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ)
    (z : Fin (p+5) → ℝ) :
    z ∈ chgWfull p κ f ↔
      (Fin.snoc (fun i : Fin p => z (Fin.castAdd 5 i)) (z (chgY p)) ∈ κ) ∧
      (z (chgU p) = Aend κ f (fun i : Fin p => z (Fin.castAdd 5 i))) ∧
      (z (chgV p) = Bend κ f (fun i : Fin p => z (Fin.castAdd 5 i))) ∧
      (z (chgW p) = f (fun i : Fin p => z (Fin.castAdd 5 i)) (z (chgY p))) ∧
      (z (chgW p) = z (chgU p) + (z (chgV p) - z (chgU p)) * z (chgT p)) := by
  simp only [chgWfull, Set.mem_inter_iff, chgSrel, Set.mem_ofPred_eq]
  rw [mem_chgSκ, mem_chgSA, mem_chgSB, mem_chgSF]
  tauto

/-! ## 7. Index computations for `Fin.append` -/

theorem chgInitInit (p : ℕ) (z : Fin (p+2) → ℝ) :
    Fin.init (Fin.init z) = (fun i : Fin p => z (Fin.castSucc (Fin.castSucc i))) := by
  funext i
  rfl

theorem chgInitLast (p : ℕ) (x : Fin (p+2) → ℝ) :
    (Fin.init x) (Fin.last p) = x (Fin.castSucc (Fin.last p)) := rfl

theorem append_chg_par (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) (i : Fin p) :
    Fin.append x w (Fin.castAdd 5 i) = x (Fin.castAdd 2 i) := by
  rw [show (Fin.castAdd 5 i : Fin (p+5)) = Fin.castAdd 3 (Fin.castAdd 2 i) from Fin.ext rfl]
  exact Fin.append_left x w (Fin.castAdd 2 i)

theorem append_chgY (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) :
    Fin.append x w (chgY p) = x (Fin.last (p+1)) := by
  rw [show chgY p = Fin.castAdd 3 (Fin.last (p+1)) from Fin.ext rfl]
  exact Fin.append_left x w (Fin.last (p+1))

theorem append_chgT (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) :
    Fin.append x w (chgT p) = x (Fin.castSucc (Fin.last p)) := by
  rw [show chgT p = Fin.castAdd 3 (Fin.castSucc (Fin.last p)) from Fin.ext rfl]
  exact Fin.append_left x w (Fin.castSucc (Fin.last p))

theorem append_chgU (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) :
    Fin.append x w (chgU p) = w 0 := by
  rw [show chgU p = Fin.natAdd (p+2) (0 : Fin 3) from Fin.ext rfl]
  exact Fin.append_right x w 0

theorem append_chgV (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) :
    Fin.append x w (chgV p) = w 1 := by
  rw [show chgV p = Fin.natAdd (p+2) (1 : Fin 3) from Fin.ext rfl]
  exact Fin.append_right x w 1

theorem append_chgW (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) :
    Fin.append x w (chgW p) = w 2 := by
  rw [show chgW p = Fin.natAdd (p+2) (2 : Fin 3) from Fin.ext rfl]
  exact Fin.append_right x w 2

theorem castSucc_castSucc_eq (p : ℕ) (i : Fin p) :
    (Fin.castSucc (Fin.castSucc i) : Fin (p+2)) = Fin.castAdd 2 i := Fin.ext rfl

/-- The parameter function of `Fin.append x w` is the parameter function of `x`. -/
theorem chgLPar_append (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 3 → ℝ) :
    (fun i : Fin p => Fin.append x w (Fin.castAdd 5 i)) = Fin.init (Fin.init x) := by
  funext i
  rw [append_chg_par]
  show x (Fin.castAdd 2 i) = x (Fin.castSucc (Fin.castSucc i))
  exact congrArg x (castSucc_castSucc_eq p i).symm

/-! ## 8. The projection identity `projN 3 Wfull = W` -/

theorem projN_chgWfull (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Work.WilG5.projN 3 (chgWfull p κ f) = chgWset p κ f := by
  ext x
  rw [Work.WilG5.projN, Set.mem_ofPred_eq, chgWset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_chgWfull p κ f] at hw
    obtain ⟨hκ, hA, hB, hF, hrel⟩ := hw
    rw [append_chgY, chgLPar_append] at hκ
    rw [append_chgU, chgLPar_append] at hA
    rw [append_chgV, chgLPar_append] at hB
    rw [append_chgW, append_chgY, chgLPar_append] at hF
    rw [append_chgW, append_chgU, append_chgV, append_chgT] at hrel
    refine ⟨hκ, ?_⟩
    rw [hA, hB] at hrel
    rw [hF] at hrel
    exact hrel
  · rintro ⟨hκ, hrel⟩
    refine ⟨![Aend κ f (Fin.init (Fin.init x)), Bend κ f (Fin.init (Fin.init x)),
      f (Fin.init (Fin.init x)) (x (Fin.last (p+1)))], ?_⟩
    rw [mem_chgWfull p κ f]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [append_chgY, chgLPar_append]; exact hκ
    · rw [append_chgU, chgLPar_append]; simp
    · rw [append_chgV, chgLPar_append]; simp
    · rw [append_chgW, append_chgY, chgLPar_append]; simp
    · rw [append_chgW, append_chgU, append_chgV, append_chgT]
      simpa using hrel

/-! ## 9. Membership in `E` -/

theorem mem_chgE (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ)
    (x : Fin (p+1) → ℝ) :
    x ∈ chgE p κ f ↔ ∃ y : ℝ, Fin.snoc (Fin.init x) y ∈ κ ∧
      f (Fin.init x) y = Aend κ f (Fin.init x) +
        (Bend κ f (Fin.init x) - Aend κ f (Fin.init x)) * x (Fin.last p) := by
  have key : ∀ t : ℝ, (Fin.snoc x t ∈ chgWset p κ f ↔
      (Fin.snoc (Fin.init x) t ∈ κ ∧ f (Fin.init x) t = Aend κ f (Fin.init x) +
        (Bend κ f (Fin.init x) - Aend κ f (Fin.init x)) * x (Fin.last p))) := by
    intro t
    simp only [chgWset, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]
  have hE : x ∈ chgE p κ f ↔ ∃ t : ℝ, Fin.snoc x t ∈ chgWset p κ f := Iff.rfl
  rw [hE]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (key t).mp ht⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (key y).mpr hy⟩

/-! ## 10. The graph of the chart is `W ∪ (half ∩ π⁻¹ Eᶜ)` -/

theorem chartGraph_eq (p : ℕ) (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ)
    (huniq : ∀ (l : Fin p → ℝ) (t y₁ y₂ : ℝ),
      Fin.snoc l y₁ ∈ κ → f l y₁ = Aend κ f l + (Bend κ f l - Aend κ f l) * t →
      Fin.snoc l y₂ ∈ κ → f l y₂ = Aend κ f l + (Bend κ f l - Aend κ f l) * t →
      y₁ = y₂) :
    graphFam (chart1 f κ) = chgWset p κ f ∪ chgSecond p κ f := by
  ext z
  have hL : z ∈ graphFam (chart1 f κ) ↔
      z (Fin.last (p+1)) =
        chart1 f κ (Fin.init (Fin.init z)) (z (Fin.castSucc (Fin.last p))) := by
    simp only [mem_graphFam, ← chgInitInit]
  have hW : z ∈ chgWset p κ f ↔
      (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p+1))) ∈ κ ∧
        f (Fin.init (Fin.init z)) (z (Fin.last (p+1))) =
          Aend κ f (Fin.init (Fin.init z)) +
            (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
              z (Fin.castSucc (Fin.last p))) := by
    simp only [chgWset, Set.mem_ofPred_eq]
  have hE2 : Fin.init z ∈ chgE p κ f ↔
      (∃ y : ℝ, Fin.snoc (Fin.init (Fin.init z)) y ∈ κ ∧
        f (Fin.init (Fin.init z)) y = Aend κ f (Fin.init (Fin.init z)) +
          (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
            z (Fin.castSucc (Fin.last p))) := by
    rw [mem_chgE p κ f (Fin.init z)]
    simp only [chgInitLast]
  have hS : z ∈ chgSecond p κ f ↔
      (z (Fin.last (p+1)) = 1/2 ∧
        ¬ (∃ y : ℝ, Fin.snoc (Fin.init (Fin.init z)) y ∈ κ ∧
          f (Fin.init (Fin.init z)) y = Aend κ f (Fin.init (Fin.init z)) +
            (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
              z (Fin.castSucc (Fin.last p)))) := by
    simp only [chgSecond, chgHalf, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, hE2]
  rw [Set.mem_union, hL, hW, hS]
  let hex : Prop := ∃ y : ℝ, Fin.snoc (Fin.init (Fin.init z)) y ∈ κ ∧
    f (Fin.init (Fin.init z)) y = Aend κ f (Fin.init (Fin.init z)) +
      (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
        z (Fin.castSucc (Fin.last p))
  by_cases hE : hex
  · have hch : chart1 f κ (Fin.init (Fin.init z)) (z (Fin.castSucc (Fin.last p))) =
        Classical.choose hE := by
      show (if h : ∃ y : ℝ, Fin.snoc (Fin.init (Fin.init z)) y ∈ κ ∧
        f (Fin.init (Fin.init z)) y = Aend κ f (Fin.init (Fin.init z)) +
          (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
            z (Fin.castSucc (Fin.last p))
        then Classical.choose h else 1/2) = Classical.choose hE
      exact dif_pos hE
    have hspec := Classical.choose_spec hE
    constructor
    · intro h
      left
      rw [hch] at h
      refine ⟨?_, ?_⟩
      · rw [h]; exact hspec.1
      · rw [h]; exact hspec.2
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [hch]
        exact huniq (Fin.init (Fin.init z)) (z (Fin.castSucc (Fin.last p)))
          (z (Fin.last (p+1))) (Classical.choose hE) h1 h2 hspec.1 hspec.2
      · exact absurd hE h2
  · have hch : chart1 f κ (Fin.init (Fin.init z)) (z (Fin.castSucc (Fin.last p))) = 1/2 := by
      show (if h : ∃ y : ℝ, Fin.snoc (Fin.init (Fin.init z)) y ∈ κ ∧
        f (Fin.init (Fin.init z)) y = Aend κ f (Fin.init (Fin.init z)) +
          (Bend κ f (Fin.init (Fin.init z)) - Aend κ f (Fin.init (Fin.init z))) *
            z (Fin.castSucc (Fin.last p))
        then Classical.choose h else 1/2) = 1/2
      exact dif_neg hE
    constructor
    · intro h
      right
      refine ⟨?_, hE⟩
      rw [hch] at h
      exact h
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd ⟨z (Fin.last (p+1)), h1, h2⟩ hE
      · rw [hch]; exact h1

/-! ## 11. Format and degree bookkeeping -/

/-- The format produced by the substitution atom on the cell. -/
def chgFκ' (p Fκ : ℕ) : ℕ := Fκ + 2 * ((p+5) + (p+1)) + 1

/-- The format produced by the substitution atom on the family member. -/
def chgF0' (p F0 : ℕ) : ℕ := F0 + 2 * ((p+5) + (p+2)) + 1

/-- A common format for all five pieces. -/
def chgBaseF (p F0 Fκ : ℕ) : ℕ := max (max (chgFκ' p Fκ) (chgF0' p F0)) (p+5)

/-- The format constant of the theorem. -/
def chgA (p F0 Fκ : ℕ) : ℕ := chgBaseF p F0 Fκ + 12

/-- The degree polynomial of the theorem: it evaluates to `6 * bκ(D) + 2 * D + 21`. -/
def chgB (bκ : MvPolynomial (Fin 2) ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.C 6 * bκ + MvPolynomial.C 2 * MvPolynomial.X 0 + MvPolynomial.C 21

theorem chgFκ'_le (p F0 Fκ : ℕ) : chgFκ' p Fκ ≤ chgBaseF p F0 Fκ := by
  show chgFκ' p Fκ ≤ max (max (chgFκ' p Fκ) (chgF0' p F0)) (p+5)
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem chgF0'_le (p F0 Fκ : ℕ) : chgF0' p F0 ≤ chgBaseF p F0 Fκ := by
  show chgF0' p F0 ≤ max (max (chgFκ' p Fκ) (chgF0' p F0)) (p+5)
  exact le_trans (le_max_right _ _) (le_max_left _ _)

theorem chgDim_le (p F0 Fκ : ℕ) : p+5 ≤ chgBaseF p F0 Fκ := by
  show p+5 ≤ max (max (chgFκ' p Fκ) (chgF0' p F0)) (p+5)
  exact le_max_right _ _

theorem chgHalfPoly_set (p : ℕ) :
    {z : Fin (p+2) → ℝ | MvPolynomial.eval z
      (MvPolynomial.X (Fin.last (p+1)) - MvPolynomial.C (1/2)) = 0} = chgHalf p := by
  ext z
  simp only [Set.mem_ofPred_eq, chgHalf]
  rw [show MvPolynomial.eval z (MvPolynomial.X (Fin.last (p+1)) -
      MvPolynomial.C (1/2)) = z (Fin.last (p+1)) - 1/2 from by simp]
  constructor <;> intro h <;> linarith

theorem chgHalf_mem (S : SOMin) (p : ℕ) : chgHalf p ∈ S.Ω (p+2) 1 (p+2) := by
  have h := S.hyp (p+2) (MvPolynomial.X (Fin.last (p+1)) - MvPolynomial.C (1/2))
  rw [chgHalfPoly_set] at h
  exact Work.WilG5.mem_mono h (p+2) 1 le_rfl
    (by simpa using Work.WilG5.td_X_sub_C_le (Fin.last (p+1)) (1/2 : ℝ))

theorem chgB_eval (bκ : MvPolynomial (Fin 2) ℕ) (D : ℕ) :
    MvPolynomial.eval ![D, 1] (chgB bκ) =
      6 * MvPolynomial.eval ![D, 1] bκ + 2 * D + 21 := by
  unfold chgB
  simp

/-! ## 12. The theorem -/

theorem lipschitz_chart_graph (S : WilkiesDesign.SOMin) (p F0 Fκ : ℕ)
    (bκ : MvPolynomial (Fin 2) ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p+1) → ℝ)),
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        κ ∈ S.Ω Fκ (MvPolynomial.eval ![D, 1] bκ) (p + 1) →
        WilkiesDesign.graphOf (Work.WilG4a.Aend κ f) ∈ S.Ω Fκ (MvPolynomial.eval ![D, 1] bκ) (p + 1) →
        WilkiesDesign.graphOf (Work.WilG4a.Bend κ f) ∈ S.Ω Fκ (MvPolynomial.eval ![D, 1] bκ) (p + 1) →
        (∀ (l : Fin p → ℝ) (t y₁ y₂ : ℝ),
          Fin.snoc l y₁ ∈ κ → f l y₁ = Work.WilG4a.Aend κ f l + (Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) * t →
          Fin.snoc l y₂ ∈ κ → f l y₂ = Work.WilG4a.Aend κ f l + (Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) * t →
          y₁ = y₂) →
        Work.WilG4a.graphFam (Work.WilG4a.chart1 f κ) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1 + 1) := by
  refine ⟨chgA p F0 Fκ, chgB bκ, ?_⟩
  intro D f κ hf hκ hA hB huniq
  set g : ℕ := MvPolynomial.eval ![D, 1] bκ with hg
  -- the five pieces, all raised to the common format `chgBaseF p F0 Fκ`
  have hSκ : chgSκ p κ ∈ S.Ω (chgBaseF p F0 Fκ) (g+2) (p+5) :=
    mem_mono (subst_mem S (chgIotK p) hκ) (chgFκ'_le p F0 Fκ) le_rfl
  have hSA : chgSA p (Aend κ f) ∈ S.Ω (chgBaseF p F0 Fκ) (g+2) (p+5) :=
    mem_mono (subst_mem S (chgIotA p) hA) (chgFκ'_le p F0 Fκ) le_rfl
  have hSB : chgSB p (Bend κ f) ∈ S.Ω (chgBaseF p F0 Fκ) (g+2) (p+5) :=
    mem_mono (subst_mem S (chgIotB p) hB) (chgFκ'_le p F0 Fκ) le_rfl
  have hSF : chgSF p f ∈ S.Ω (chgBaseF p F0 Fκ) (D+2) (p+5) :=
    mem_mono (subst_mem S (chgIotF p) hf) (chgF0'_le p F0 Fκ) le_rfl
  have hSrel : chgSrel p ∈ S.Ω (chgBaseF p F0 Fκ) 2 (p+5) :=
    mem_mono (chgSrel_mem S p) (chgDim_le p F0 Fκ) le_rfl
  -- the intersections
  have hI1 : (chgSκ p κ ∩ chgSA p (Aend κ f)) ∈
      S.Ω (chgBaseF p F0 Fκ + 1) (2*g+4) (p+5) := by
    have h := inter_mem2 hSκ hSA
    exact mem_mono h le_rfl (by omega)
  have hI2 : ((chgSκ p κ ∩ chgSA p (Aend κ f)) ∩ chgSB p (Bend κ f)) ∈
      S.Ω (chgBaseF p F0 Fκ + 2) (3*g+6) (p+5) := by
    have hSB' : chgSB p (Bend κ f) ∈ S.Ω (chgBaseF p F0 Fκ + 1) (g+2) (p+5) :=
      mem_mono hSB (by omega) le_rfl
    have h := inter_mem2 hI1 hSB'
    exact mem_mono h le_rfl (by omega)
  have hI3 : (chgSF p f ∩ chgSrel p) ∈ S.Ω (chgBaseF p F0 Fκ + 2) (D+4) (p+5) := by
    have h := inter_mem2 hSF hSrel
    exact mem_mono h (by omega) (by omega)
  have hI4 : chgWfull p κ f ∈ S.Ω (chgBaseF p F0 Fκ + 3) (3*g+D+10) (p+5) := by
    have h := inter_mem2 hI2 hI3
    exact mem_mono h le_rfl (by omega)
  -- projection: `chgWset`
  have hProjN : Work.WilG5.projN 3 (chgWfull p κ f) ∈
      S.Ω (chgBaseF p F0 Fκ + 6) (3*g+D+10) (p+2) :=
    Work.WilG5.projN_mem (n := p+2) 3 (chgBaseF p F0 Fκ + 3) (3*g+D+10) hI4
  rw [projN_chgWfull] at hProjN
  -- `E`, its complement and the pull-back
  have hE : chgE p κ f ∈ S.Ω (chgBaseF p F0 Fκ + 7) (3*g+D+10) (p+1) := S.proj hProjN
  have hEc : (chgE p κ f)ᶜ ∈ S.Ω (chgBaseF p F0 Fκ + 8) (3*g+D+10) (p+1) := S.compl hE
  have hPi : {z : Fin (p+2) → ℝ | Fin.init z ∈ (chgE p κ f)ᶜ} ∈
      S.Ω (chgBaseF p F0 Fκ + 9) (3*g+D+10) (p+2) := S.prod_right hEc
  -- the second piece
  have hHalf : chgHalf p ∈ S.Ω (chgBaseF p F0 Fκ + 9) 1 (p+2) :=
    mem_mono (chgHalf_mem S p) (by have := chgDim_le p F0 Fκ; omega) le_rfl
  have hSecond : chgSecond p κ f ∈ S.Ω (chgBaseF p F0 Fκ + 10) (3*g+D+11) (p+2) := by
    have h := inter_mem2 hHalf hPi
    exact mem_mono h le_rfl (by omega)
  -- the union
  have hW' : chgWset p κ f ∈ S.Ω (chgBaseF p F0 Fκ + 10) (3*g+D+10) (p+2) :=
    mem_mono hProjN (by omega) le_rfl
  have hUnion : chgWset p κ f ∪ chgSecond p κ f ∈
      S.Ω (chgBaseF p F0 Fκ + 10) (6*g+2*D+21) (p+2) := by
    have h := union_mem hW' hSecond
    exact mem_mono h le_rfl (by omega)
  rw [← chartGraph_eq p κ f huniq] at hUnion
  have hfmt : chgBaseF p F0 Fκ + 10 ≤ chgA p F0 Fκ := by unfold chgA; omega
  have hdeg : (6*g+2*D+21) ≤ MvPolynomial.eval ![D, 1] (chgB bκ) := by
    rw [chgB_eval]
  exact mem_mono hUnion hfmt hdeg

end Work.WilG4a

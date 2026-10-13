/-
  WilG4c — the "clamped, regrouped family graph" lemma (BNZ §5.2 bookkeeping).

  `vieClampGraph` is the `Ω`-membership input of the reduction `StepYbdd` of
  `Submission/Work/WilG4c`.  It says: if every member `F i` of a family of `n+1`-variable
  functions has an `Ω F0 D`-bounded graph, then the family obtained by

  * moving the distinguished first variable `x` of `F i` into the parameter space
    (`vie F i w y = F i (w ∘ castSucc) (cons (w last) y)`), and
  * clamping the values into `(0,1)` (`t ↦ t` on `(0,1)`, `t ↦ 1/2` outside),

  has `Ω (F0+a) (D+c)`-bounded graphs, with `a, c` depending only on `p` and `n`.

  Two facts are used:

  * **Reindexing.**  `famGraph (F i) ⊆ ℝ^{p+(n+1)+1}` and `famGraph (vie F i) ⊆ ℝ^{(p+1)+n+1}`
    describe the *same* graph on the same coordinates: the value preserving identification
    `Fin.cast` of the two index types carries one to the other.  This is `reindex_famGraph`
    (coordinate pullback is one of the closure axioms, packaged in `Work.WilG4c.Subst`).

  * **Clamping.**  The clamped graph is the graph of the *composite* `clamp ∘ ψ`, where `ψ` is
    the function whose graph is `famGraph (vie F i)`.  Composition uses the hypothesis graph
    exactly once, whence the degree grows by a constant only — the naive decomposition into
    "value in `(0,1)`" and "value outside" pieces would use `famGraph` twice and cost `2 * D`
    (`Ω`-degrees add under unions and intersections).  It is split into `clampGraphMem`
    (the fixed relation `t = clamp s` is `Ω`-bounded in absolute format/degree) and
    `graphOfScalarComp` (composing a scalar `Ω`-map with an `Ω`-graph costs only additive
    degrees).

  `vieRead` is written in the very spelling produced by `famGraph`: the `(n+1)`-vector of
  `(x,y)` is the `Fin.cons` of the `x`-coordinate and the `n` `y`-coordinates, so that
  `famGraph_vieClamp` is definitional.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.Subst
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4c.clampGraphMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- The reading of a family `F` of `(n+1)`-variable functions in the coordinates of the
regrouped family `(w,y) ↦ F (w ∘ castSucc) (cons (w last) y)`: the `(p+1)+n` coordinates
`w ++ y` are read as the `p` parameters `w 0 .. w (p-1)`, the variable `x = w p` and the `n`
variables `w (p+1) .. w (p+n)`. -/
def vieRead {p n : ℕ} (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    (Fin ((p + 1) + n) → ℝ) → ℝ :=
  fun u => F (fun a : Fin p => u (Fin.castAdd n a.castSucc))
    (Fin.cons (u (Fin.castAdd n (Fin.last p))) (fun j : Fin n => u (Fin.natAdd (p + 1) j)))

/-- **Clamping.**  The graph of the clamped regrouped family is the graph of the clamp
composed with `vieRead F`; by the spelling of `vieRead` this is definitional. -/
theorem famGraph_vieClamp (p n : ℕ) (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    famGraph (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        if F (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) ∈ Set.Ioo (0 : ℝ) 1
        then F (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) else (1 / 2 : ℝ))
      = graphOf (fun v : Fin ((p + 1) + n) → ℝ =>
          if vieRead F v ∈ Set.Ioo (0 : ℝ) 1 then vieRead F v else (1 / 2 : ℝ)) := by
  show graphOf (fun v : Fin ((p + 1) + n) → ℝ =>
      (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        if F (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) ∈ Set.Ioo (0 : ℝ) 1
        then F (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) else (1 / 2 : ℝ))
      (fun i : Fin (p + 1) => v (Fin.castAdd n i)) (fun j : Fin n => v (Fin.natAdd (p + 1) j)))
    = graphOf (fun v : Fin ((p + 1) + n) → ℝ =>
        if vieRead F v ∈ Set.Ioo (0 : ℝ) 1 then vieRead F v else (1 / 2 : ℝ))
  congr 1

/-- **Reindexing.**  Along the (value preserving) identification
`Fin (p + (n+1) + 1) → Fin ((p+1) + n + 1)`, the graph of `F` is the graph of `vieRead F`. -/
theorem reindex_famGraph (p n : ℕ) (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (h : p + (n + 1) + 1 = (p + 1) + n + 1) :
    {w : Fin ((p + 1) + n + 1) → ℝ |
        w ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i) ∈ famGraph F}
      = graphOf (vieRead F) := by
  ext z
  simp only [famGraph, graphOf]
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  have hL : (z ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i))
      (Fin.last (p + (n + 1))) = z (Fin.last ((p + 1) + n)) := by
    simp only [Function.comp_apply]
    exact congrArg z (Fin.ext (by simp only [Fin.val_cast, Fin.val_last]; omega))
  have hR : F (fun a : Fin p =>
          (Fin.init (z ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i)))
            (Fin.castAdd (n + 1) a))
        (fun j : Fin (n + 1) =>
          (Fin.init (z ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i)))
            (Fin.natAdd p j))
      = vieRead F (Fin.init z) := by
    simp only [vieRead]
    have h1 : (fun a : Fin p =>
          (Fin.init (z ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i)))
            (Fin.castAdd (n + 1) a))
        = (fun a : Fin p => (Fin.init z) (Fin.castAdd n a.castSucc)) := by
      funext a
      simp only [Fin.init, Function.comp_apply]
      exact congrArg z (Fin.ext (by simp))
    have h2 : (fun j : Fin (n + 1) =>
          (Fin.init (z ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i)))
            (Fin.natAdd p j))
        = Fin.cons ((Fin.init z) (Fin.castAdd n (Fin.last p)))
            (fun j : Fin n => (Fin.init z) (Fin.natAdd (p + 1) j)) := by
      funext jj
      show (Fin.init (z ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast h i))) (Fin.natAdd p jj)
        = (Fin.cons ((Fin.init z) (Fin.castAdd n (Fin.last p)))
            (fun j : Fin n => (Fin.init z) (Fin.natAdd (p + 1) j)) : Fin (n + 1) → ℝ) jj
      refine Fin.cases ?_ ?_ jj
      · rw [Fin.cons_zero]
        simp only [Fin.init, Function.comp_apply]
        exact congrArg z (Fin.ext (by simp))
      · intro k
        rw [Fin.cons_succ]
        simp only [Fin.init, Function.comp_apply]
        exact congrArg z (Fin.ext
          (by simp only [Fin.val_cast, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ]; omega))
    rw [h1, h2]
  rw [hL, hR]

/-! ## Composing a scalar `Ω`-map with an `Ω`-graph

The graph of `x ↦ g (phi x)`, where `g : ℝ → ℝ` and `phi : ℝ^m → ℝ` both have `Ω`-graphs, is
`Ω`-bounded with formats/degrees *added*: put the value `u` of `phi` into an extra coordinate of
`ℝ^{m+2}` (a coordinate pullback of `graphOf phi`, costing `D₁ + 2`), impose the fixed relation
`y = g u` between the last two coordinates (a coordinate pullback of `graphOf g ⊆ ℝ²`, costing
`D₂ + 2`, where `g` is read on the constant `Fin 1`-vector), and project the `u`-coordinate away.
`graphOf phi` occurs exactly once, so the degree is `D₁ + D₂ + 4`. -/

/-- In `ℝ^{m+2}` with coordinates `(x, y, u)`, the substitution selecting `(x, u)`. -/
def sigAU (m : ℕ) : Fin (m + 1) → Fin (m + 2) :=
  Fin.snoc (fun i : Fin m => Fin.castSucc (Fin.castSucc i)) (Fin.last (m + 1))

/-- In `ℝ^{m+2}` with coordinates `(x, y, u)`, the substitution selecting `(u, y)`. -/
def sigBY (m : ℕ) : Fin 2 → Fin (m + 2) :=
  Fin.cons (Fin.last (m + 1)) (fun _ : Fin 1 => Fin.castSucc (Fin.last m))

theorem sigAU_castSucc (m : ℕ) (i : Fin m) :
    sigAU m (Fin.castSucc i) = Fin.castSucc (Fin.castSucc i) := by
  simp [sigAU]

theorem sigAU_last (m : ℕ) : sigAU m (Fin.last m) = Fin.last (m + 1) := by
  simp [sigAU]

theorem sigBY_zero (m : ℕ) : sigBY m 0 = Fin.last (m + 1) := by
  simp [sigBY, Fin.cons_zero]

theorem sigBY_last (m : ℕ) : sigBY m (Fin.last 1) = Fin.castSucc (Fin.last m) := by
  have h : (Fin.last 1 : Fin 2) = Fin.succ (0 : Fin 1) := by
    apply Fin.ext
    simp [Fin.val_last, Fin.val_succ]
  simp only [sigBY, h, Fin.cons_succ]

/-- Membership in the `(x,u)`-pullback of `graphOf phi`, on a vector `Fin.snoc x t`. -/
theorem memA_snoc {m : ℕ} (phi : (Fin m → ℝ) → ℝ) (x : Fin (m + 1) → ℝ) (t : ℝ) :
    Fin.snoc x t ∈ {z : Fin (m + 2) → ℝ | z ∘ sigAU m ∈ graphOf phi} ↔
      t = phi (Fin.init x) := by
  have h1 : (Fin.snoc x t ∘ sigAU m) (Fin.last m) = t := by
    rw [Function.comp_apply, sigAU_last, Fin.snoc_last]
  have h2 : Fin.init (Fin.snoc x t ∘ sigAU m) = Fin.init x := by
    funext k
    show ((Fin.snoc x t : Fin (m + 2) → ℝ)) (sigAU m (Fin.castSucc k)) = x (Fin.castSucc k)
    rw [sigAU_castSucc, Fin.snoc_castSucc]
  show ((Fin.snoc x t ∘ sigAU m) (Fin.last m) = phi (Fin.init (Fin.snoc x t ∘ sigAU m))) ↔
      t = phi (Fin.init x)
  constructor
  · intro h
    rwa [h1, h2] at h
  · intro h
    rwa [h1, h2]

/-- Membership in the `(u,y)`-pullback of `graphOf g`, on a vector `Fin.snoc x t`. -/
theorem memB_snoc {m : ℕ} (g : (Fin 1 → ℝ) → ℝ) (x : Fin (m + 1) → ℝ) (t : ℝ) :
    Fin.snoc x t ∈ {z : Fin (m + 2) → ℝ | z ∘ sigBY m ∈ graphOf g} ↔
      x (Fin.last m) = g (fun _ : Fin 1 => t) := by
  have h1 : (Fin.snoc x t ∘ sigBY m) 0 = t := by
    rw [Function.comp_apply, sigBY_zero, Fin.snoc_last]
  have h2 : (Fin.snoc x t ∘ sigBY m) (Fin.last 1) = x (Fin.last m) := by
    rw [Function.comp_apply, sigBY_last, Fin.snoc_castSucc]
  have h3 : Fin.init (Fin.snoc x t ∘ sigBY m) = (fun _ : Fin 1 => t) := by
    funext k
    have hk : Fin.castSucc k = (0 : Fin 2) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_zero]
      omega
    show (Fin.snoc x t ∘ sigBY m) (Fin.castSucc k) = t
    rw [hk]
    exact h1
  show ((Fin.snoc x t ∘ sigBY m) (Fin.last 1) = g (Fin.init (Fin.snoc x t ∘ sigBY m))) ↔
      x (Fin.last m) = g (fun _ : Fin 1 => t)
  constructor
  · intro h
    rwa [h2, h3] at h
  · intro h
    rwa [h2, h3]

/-- Projecting the value coordinate of the two pullbacks gives the graph of `g ∘ phi`. -/
theorem projLast_inter_eq {m : ℕ} (g : (Fin 1 → ℝ) → ℝ) (phi : (Fin m → ℝ) → ℝ) :
    projLast ({z : Fin (m + 2) → ℝ | z ∘ sigAU m ∈ graphOf phi} ∩
        {z : Fin (m + 2) → ℝ | z ∘ sigBY m ∈ graphOf g})
      = graphOf (fun x : Fin m → ℝ => g (fun _ : Fin 1 => phi x)) := by
  ext x
  have hL : x ∈ projLast ({z : Fin (m + 2) → ℝ | z ∘ sigAU m ∈ graphOf phi} ∩
        {z : Fin (m + 2) → ℝ | z ∘ sigBY m ∈ graphOf g}) ↔
      (∃ t : ℝ, Fin.snoc x t ∈ ({z : Fin (m + 2) → ℝ | z ∘ sigAU m ∈ graphOf phi} ∩
        {z : Fin (m + 2) → ℝ | z ∘ sigBY m ∈ graphOf g})) := Iff.rfl
  have hR : x ∈ graphOf (fun x : Fin m → ℝ => g (fun _ : Fin 1 => phi x)) ↔
      (x (Fin.last m) = g (fun _ : Fin 1 => phi (Fin.init x))) := Iff.rfl
  rw [hL, hR]
  constructor
  · rintro ⟨t, ht⟩
    rw [Set.mem_inter_iff] at ht
    obtain ⟨ha, hb⟩ := ht
    rw [memA_snoc] at ha
    rw [memB_snoc] at hb
    rw [ha] at hb
    exact hb
  · intro hx
    refine ⟨phi (Fin.init x), ?_⟩
    rw [Set.mem_inter_iff]
    exact ⟨by rw [memA_snoc], by rw [memB_snoc]; exact hx⟩

/-- **Composition of a scalar `Ω`-map with an `Ω`-graph**, with explicit additive bounds. -/
theorem graphOfScalarComp (S : SOMin) (m : ℕ) : ∃ (C1 C2 : ℕ),
    ∀ (F1 F2 D1 D2 : ℕ) (g : (Fin 1 → ℝ) → ℝ) (phi : (Fin m → ℝ) → ℝ),
      graphOf g ∈ S.Ω F2 D2 (1 + 1) →
      graphOf phi ∈ S.Ω F1 D1 (m + 1) →
      graphOf (fun x : Fin m → ℝ => g (fun _ : Fin 1 => phi x))
        ∈ S.Ω (F1 + F2 + C1) (D1 + D2 + C2) (m + 1) := by
  refine ⟨(2 * ((m + 2) + (m + 1)) + 1) + (2 * ((m + 2) + 2) + 1) + 1 + 1, 4, ?_⟩
  intro F1 F2 D1 D2 g phi hg hphi
  have hA : {z : Fin (m + 2) → ℝ | z ∘ sigAU m ∈ graphOf phi} ∈
      S.Ω (F1 + 2 * ((m + 2) + (m + 1)) + 1) (D1 + 2) (m + 2) :=
    GraphComp.subst_mem S (sigAU m) hphi
  have hB : {z : Fin (m + 2) → ℝ | z ∘ sigBY m ∈ graphOf g} ∈
      S.Ω (F2 + 2 * ((m + 2) + 2) + 1) (D2 + 2) (m + 2) :=
    GraphComp.subst_mem S (sigBY m) hg
  have hA' : {z : Fin (m + 2) → ℝ | z ∘ sigAU m ∈ graphOf phi} ∈
      S.Ω (F1 + F2 + ((2 * ((m + 2) + (m + 1)) + 1) + (2 * ((m + 2) + 2) + 1)))
        (D1 + 2) (m + 2) :=
    Omega.mono hA (by omega) le_rfl
  have hB' : {z : Fin (m + 2) → ℝ | z ∘ sigBY m ∈ graphOf g} ∈
      S.Ω (F1 + F2 + ((2 * ((m + 2) + (m + 1)) + 1) + (2 * ((m + 2) + 2) + 1)))
        (D2 + 2) (m + 2) :=
    Omega.mono hB (by omega) le_rfl
  have hI := Omega_inter2 hA' hB'
  have hP := S.proj hI
  rw [projLast_inter_eq g phi] at hP
  exact Omega.mono hP (by omega) (by omega)

theorem vieClampGraph (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a c : ℕ),
      ∀ {k : ℕ} (F : Fin k → (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (F0 D : ℕ),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        ∀ i, WilkiesDesign.CG.famGraph
              (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
                if F i (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) ∈ Set.Ioo (0 : ℝ) 1
                then F i (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) else (1 / 2 : ℝ)) ∈
            S.Ω (F0 + a) (D + c) ((p + 1) + n + 1) := by
  -- the two ingredients: the fixed clamp relation and scalar composition
  obtain ⟨aY, cY, hY⟩ := clampGraphMem S
  obtain ⟨C1, C2, hC⟩ := graphOfScalarComp S ((p + 1) + n)
  refine ⟨((p + 1) + n + 1) + (p + (n + 1) + 1) + 1 + (p + (n + 1) + 1) + aY + C1,
    2 + cY + C2, ?_⟩
  intro k F F0 D hF i
  have hh : p + (n + 1) + 1 = (p + 1) + n + 1 := by omega
  -- 1. reindex the hypothesis graph into the coordinates of the regrouped family
  have hsub : {w : Fin ((p + 1) + n + 1) → ℝ |
      w ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast hh i) ∈ famGraph (F i)} ∈
      S.Ω (max (F0 + ((p + 1) + n + 1))
              (((p + 1) + n + 1) + (p + (n + 1) + 1)) + 1 + (p + (n + 1) + 1))
        (D + 2) ((p + 1) + n + 1) :=
    Subst S (fun i : Fin (p + (n + 1) + 1) => Fin.cast hh i) (hF i)
  rw [reindex_famGraph p n (F i) hh] at hsub
  -- 2. compose with the clamp
  have hres := hC (max (F0 + ((p + 1) + n + 1))
        (((p + 1) + n + 1) + (p + (n + 1) + 1)) + 1 + (p + (n + 1) + 1))
      aY (D + 2) cY
      (fun v : Fin 1 → ℝ => if v 0 ∈ Set.Ioo (0 : ℝ) 1 then v 0 else (1 / 2 : ℝ))
      (vieRead (F i)) hY hsub
  -- 3. identify the set with the clamped graph of the regrouped family
  have hgoal : graphOf (fun v : Fin ((p + 1) + n) → ℝ =>
        if vieRead (F i) v ∈ Set.Ioo (0 : ℝ) 1 then vieRead (F i) v else (1 / 2 : ℝ)) ∈
      S.Ω (max (F0 + ((p + 1) + n + 1))
              (((p + 1) + n + 1) + (p + (n + 1) + 1)) + 1 + (p + (n + 1) + 1) + aY + C1)
        ((D + 2) + cY + C2) ((p + 1) + n + 1) := hres
  rw [← famGraph_vieClamp p n (F i)] at hgoal
  -- 4. format/degree bookkeeping
  refine Omega.mono hgoal ?_ ?_
  · have hmax : max (F0 + ((p + 1) + n + 1)) (((p + 1) + n + 1) + (p + (n + 1) + 1)) ≤
        F0 + ((p + 1) + n + 1) + (p + (n + 1) + 1) := max_le (by omega) (by omega)
    omega
  · omega

end Work.WilG4c

/-
  Subproject WilE9G / Assembly — the auxiliary lemmas of the final assembly.

  This module collects the pieces of `Work.WilE9G.EffStratAE_of_frozen` that do not mention the
  assembly data (the list of strata, the direction `c`, the null sets): the elementary cube facts,
  the box-free packaging of the a.e. nondegeneracy, the per-basic ambient stratification, and the
  format/degree bookkeeping of `ambCatX` + `lagStratumAE`.
-/
import Mathlib
import Submission.Work.WilE9G.Defs
import Submission.Work.WilE9G.Collapse
import Submission.Work.WilE9G.Cover
import Submission.Work.WilE9G.G1
import Submission.Work.WilE9G.Sard.exists_null_of_Good_amb
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Assembly.Step3
import Submission.Work.WilE9G.Assembly.exists_ambStrata
import Submission.Work.WilE9G.Assembly.exists_null_of_degenerate_all
import Submission.Work.WilE9G.Assembly.ambCatX_props
import Submission.Work.WilE9G.Assembly.poly_eval_mono
import Submission.Work.WilE9G.Assembly.masterPoly_bound
import Submission.Work.WilE9G.Assembly.atomDeg_pos_prod_le_basic
import Submission.Work.WilE9G.Assembly.lagStratumAE_fmt
import Submission.Work.WilE9G.Assembly.ambStratum_j_le_ambient

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G

open WilkiesDesign WilkiesDesign.E Work.WilE9G.Lagrange
open Work.WilE9G.Assembly

/-! ## Elementary list and cube lemmas -/

/-- A crude length bound for a flat map. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ n) : (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 : (f a).length ≤ n := h a List.mem_cons_self
    have h2 : (t.flatMap f).length ≤ t.length * n :=
      ih fun b hb => h b (List.mem_cons_of_mem a hb)
    calc (f a).length + (t.flatMap f).length ≤ n + t.length * n := Nat.add_le_add h1 h2
      _ = (t.length + 1) * n := by ring

/-- `decide p = true` gives `p`. -/
theorem of_decide_true {p : Prop} [Decidable p] (h : decide p = true) : p := by
  rwa [decide_eq_true_eq] at h

/-- `p` gives `decide p = true`. -/
theorem decide_true_of {p : Prop} [Decidable p] (h : p) : decide p = true := by
  rw [decide_eq_true_eq]; exact h

/-- The cube is convex. -/
theorem convex_cubeC (k : ℕ) : Convex ℝ (cubeC k) := by
  rw [cubeC_eq_pi]
  exact convex_pi (fun _ _ => convex_Icc (-1 : ℝ) 1)

/-- The projection of the cube is the cube. -/
theorem stratProj_image_cubeC {n m : ℕ} :
    Work.WilE9.Sharp.stratProj '' cubeC (n + (1 + m)) = cubeC (n + 1) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    exact hw _
  · intro hy
    refine ⟨fun j => if h : (j : ℕ) < n + 1 then y ⟨j, h⟩ else 0, ?_, ?_⟩
    · intro j
      by_cases h : (j : ℕ) < n + 1
      · show |(if h : (j : ℕ) < n + 1 then y ⟨j, h⟩ else (0 : ℝ))| ≤ 1
        rw [dif_pos h]
        exact hy _
      · show |(if h : (j : ℕ) < n + 1 then y ⟨j, h⟩ else (0 : ℝ))| ≤ 1
        rw [dif_neg h]
        norm_num
    · funext i
      rw [Work.WilE9G.stratProj_apply]
      have hval : ((Work.WilE9.Sharp.stratInj (Fin.castAdd m i) : Fin (n + (1 + m))) : ℕ)
          = i.val := rfl
      have h : ((Work.WilE9.Sharp.stratInj (Fin.castAdd m i) : Fin (n + (1 + m))) : ℕ) < n + 1 := by
        rw [hval]; exact i.isLt
      show (if h' : ((Work.WilE9.Sharp.stratInj (Fin.castAdd m i) : Fin (n + (1 + m))) : ℕ) < n + 1
        then y ⟨_, h'⟩ else (0 : ℝ)) = y i
      rw [dif_pos h]
      exact congrArg y (Fin.ext rfl)

/-- **The covering clause is vacuous when `X.set` is the whole cube.** -/
theorem not_finite_fibre_of_set_eq_cubeC {n m : ℕ}
    {X : SemiPf (n + (1 + m))} (hX : X.set = cubeC (n + (1 + m)))
    (z₀ : Fin (n + (1 + m)) → ℝ) (hz₀ : z₀ ∈ X.set) :
    ∀ y ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀,
      ¬ ({y' | y' ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ ∧
          Fin.init y' = Fin.init y}).Finite := by
  intro y hy hfin
  have hzc : z₀ ∈ cubeC (n + (1 + m)) := by rw [← hX]; exact hz₀
  have hcomp : connectedComponentIn X.set z₀ = cubeC (n + (1 + m)) := by
    rw [hX]
    refine le_antisymm (connectedComponentIn_subset _ _) fun u hu => ?_
    exact IsPreconnected.subset_connectedComponentIn (s := cubeC (n + (1 + m)))
      (x := z₀) (convex_cubeC _).isPreconnected hzc subset_rfl hu
  have hycube : y ∈ cubeC (n + 1) := by
    obtain ⟨w, hw, rfl⟩ := hy
    intro i
    exact (connectedComponentIn_subset _ _ hw).1 _
  have key : ∀ s : ℝ, |s| ≤ 1 → Fin.snoc (Fin.init y) s ∈
      {y' | y' ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ ∧
        Fin.init y' = Fin.init y} := by
    intro s hs
    constructor
    · rw [hcomp, stratProj_image_cubeC]
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hycube (Fin.castSucc k)
      · rw [Fin.snoc_last]
        exact hs
    · simp
  haveI : Infinite (Set.Icc (-1 : ℝ) 1) :=
    Set.infinite_coe_iff.mpr (Set.Icc_infinite (show (-1 : ℝ) < 1 by norm_num))
  have hinj : Function.Injective (fun s : Set.Icc (-1 : ℝ) 1 =>
      Fin.snoc (Fin.init y) (s : ℝ)) := by
    intro a b hab
    exact Subtype.ext (by simpa using congrFun hab (Fin.last n))
  have hrange : (Set.range (fun s : Set.Icc (-1 : ℝ) 1 =>
      Fin.snoc (Fin.init y) (s : ℝ))).Infinite := Set.infinite_range_of_injective hinj
  refine hrange (hfin.subset ?_)
  rintro y' ⟨s, rfl⟩
  exact key s (abs_le.mpr ⟨s.2.1, s.2.2⟩)

/-! ## The a.e. nondegeneracy, packaged -/

/-- The a.e.-nondegeneracy statement of `Assembly.exists_null_of_degenerate_all`, with the base
null set packaged as a function of the direction. -/
theorem exists_null_of_degenerate_boxfree {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hS : S.Good) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (hPhi : ∀ z ∈ S.X.set, 0 < eaEval S.X.c Phi z) :
    ∃ (Nc : Set (Fin (1 + m) → ℝ)) (Nx : (Fin (1 + m) → ℝ) → Set (Fin n → ℝ)),
      volume Nc = 0 ∧ (∀ c, volume (Nx c) = 0) ∧
      ∀ c ∉ Nc, ∀ x ∉ Nx c, ∀ z ∈ S.X.set, projBase (Nat.le_add_right n (1 + m)) z = x →
        ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ), LagEq S Phi c z mu mu0 → LagNorm mu mu0 →
          (lagJac S Phi c z mu mu0).det ≠ 0 := by
  classical
  obtain ⟨Nc, hNc0, h⟩ := Assembly.exists_null_of_degenerate_all S hS Phi hPhi
  have hex : ∀ c : Fin (1 + m) → ℝ, ∃ Nx : Set (Fin n → ℝ), volume Nx = 0 ∧
      (c ∉ Nc → ∀ x ∉ Nx, ∀ z ∈ S.X.set, projBase (Nat.le_add_right n (1 + m)) z = x →
        ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ), LagEq S Phi c z mu mu0 → LagNorm mu mu0 →
          (lagJac S Phi c z mu mu0).det ≠ 0) := by
    intro c
    by_cases hc : c ∉ Nc
    · exact ⟨(h c hc).choose, (h c hc).choose_spec.1, fun _ => (h c hc).choose_spec.2⟩
    · exact ⟨∅, by simp, fun hc' => absurd hc' hc⟩
  choose Nx hNx0 hNxconcl using hex
  exact ⟨Nc, Nx, hNc0, hNx0, fun c hc x hx z hz hproj mu mu0 hEq hNorm =>
    hNxconcl c hc x hx z hz hproj mu mu0 hEq hNorm⟩

/-- The two null sets of a single ambient stratum: the base-critical values and the degenerate
Lagrange points (for every direction outside `Nc`). -/
theorem exists_null_of_degenerate_stratum {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hS : S.Good) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (hPhi : ∀ z ∈ S.X.set, 0 < eaEval S.X.c Phi z) :
    ∃ (Nc : Set (Fin (1 + m) → ℝ)) (Nx : (Fin (1 + m) → ℝ) → Set (Fin n → ℝ))
      (N1 : Set (Fin n → ℝ)),
      volume Nc = 0 ∧ (∀ c, volume (Nx c) = 0) ∧ volume N1 = 0 ∧
      (∀ c ∉ Nc, ∀ x ∉ Nx c, ∀ z ∈ S.X.set, projBase (Nat.le_add_right n (1 + m)) z = x →
        ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ), LagEq S Phi c z mu mu0 → LagNorm mu mu0 →
          (lagJac S Phi c z mu mu0).det ≠ 0) ∧
      (∀ z ∈ S.X.set, ¬ S.IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) z →
        projBase (Nat.le_add_right n (1 + m)) z ∈ N1) := by
  obtain ⟨Nc, Nx, hNc0, hNx0, hconcl⟩ := exists_null_of_degenerate_boxfree S hS Phi hPhi
  obtain ⟨N1, hN10, hN1concl⟩ :=
    Work.WilE9G.Sard.exists_null_of_Good_amb (Nat.le_add_right n (1 + m)) S hS
  exact ⟨Nc, Nx, N1, hNc0, hNx0, hN10, hconcl, hN1concl⟩

/-! ## The ambient stratification of a single basic -/

/-- **The ambient stratification of a single basic of `X0`**, with the empty strata removed: from
the ambient `E5_strat` (`h5`, in the `AmbStratum` form) one gets, for every basic of `X0`, a list
of `Good` ambient strata whose union is exactly the piece cut out by that basic, with uniform
format bound `a5` and degree/disjunct bounds `b5 X.deg`, and with every stratum's set nonempty. -/
theorem exists_ambStrata_of_basic {n m F : ℕ} (X0 : SemiPf (n + (1 + m))) (hX0fmt : X0.fmt ≤ F)
    (a5 : ℕ) (b5 : Polynomial ℕ)
    (h5 : ∀ (N : ℕ) (X : SemiPf N), X.fmt ≤ F →
      ∃ L : List (Work.WilE9G.AmbStratum N), L.length ≤ b5.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a5 ∧ S.deg ≤ b5.eval X.deg ∧
          S.X.basics.length ≤ b5.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set)) :
    ∀ i : Fin X0.basics.length, ∃ LB : List (Work.WilE9G.AmbStratum (n + (1 + m))),
      (LB.length ≤ b5.eval (X0.basics.get i).deg ∧
        (∀ S ∈ LB, S.X.fmt ≤ a5 ∧ S.deg ≤ b5.eval (X0.basics.get i).deg ∧
          S.X.basics.length ≤ b5.eval (X0.basics.get i).deg ∧ S.Good ∧ S.X.set.Nonempty) ∧
        (⟨X0.r, X0.c, [X0.basics.get i]⟩ : SemiPf (n + (1 + m))).set = ⋃ S ∈ LB, S.X.set) := by
  intro i
  have hfmti : (⟨X0.r, X0.c, [X0.basics.get i]⟩ : SemiPf (n + (1 + m))).fmt ≤ F := by
    show (n + (1 + m)) + X0.r ≤ F
    have h2 : X0.fmt = (n + (1 + m)) + X0.r := rfl
    omega
  obtain ⟨L, hlen, hgood, hunion⟩ := h5 (n + (1 + m))
    ⟨X0.r, X0.c, [X0.basics.get i]⟩ hfmti
  refine ⟨L.filter (fun S => decide (S.X.set.Nonempty)), ?_, ?_, ?_⟩
  · exact le_trans (List.length_filter_le _ _) hlen
  · intro S hS
    rw [List.mem_filter] at hS
    exact ⟨(hgood S hS.1).1, (hgood S hS.1).2.1, (hgood S hS.1).2.2.1,
      (hgood S hS.1).2.2.2, of_decide_true hS.2⟩
  · rw [hunion]
    ext z
    constructor
    · intro hz
      obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr ⟨S, List.mem_filter.mpr ⟨hS, by
        rw [decide_eq_true_eq]; exact ⟨z, hzS⟩⟩, hzS⟩
    · intro hz
      obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr ⟨S, (List.mem_filter.mp hS).1, hzS⟩

/-- A stratum of the list of a basic is contained in that basic's piece: its points lie in `X0.set`
and satisfy the basic's conditions. -/
theorem basic_holds_of_union {n m : ℕ} (X0 : SemiPf (n + (1 + m)))
    (B : Basic (n + (1 + m)) X0.r) (hBmem : B ∈ X0.basics)
    (LB : List (Work.WilE9G.AmbStratum (n + (1 + m))))
    (hunion : (⟨X0.r, X0.c, [B]⟩ : SemiPf (n + (1 + m))).set = ⋃ S ∈ LB, S.X.set)
    {T : Work.WilE9G.AmbStratum (n + (1 + m))} (hT : T ∈ LB) :
    T.X.set ⊆ X0.set ∧ ∀ z ∈ T.X.set, B.holds X0.c z := by
  have hmem : ∀ z ∈ T.X.set, z ∈ (⟨X0.r, X0.c, [B]⟩ : SemiPf (n + (1 + m))).set := by
    intro z hz
    rw [hunion]
    exact Set.mem_iUnion₂.mpr ⟨T, hT, hz⟩
  constructor
  · intro z hz
    obtain ⟨hzc, B2, hB2mem, hB2h⟩ := hmem z hz
    rw [List.mem_singleton] at hB2mem
    rw [hB2mem] at hB2h
    exact ⟨hzc, B, hBmem, hB2h⟩
  · intro z hz
    obtain ⟨-, B2, hB2mem, hB2h⟩ := hmem z hz
    rw [List.mem_singleton] at hB2mem
    rwa [hB2mem] at hB2h

/-! ## Goodness and positivity after adjoining a chain -/

/-- Adjoining the chain of `X0` to an ambient stratum `T` does not change its `Good`, makes the
lifted weight `Φ_B = ∏_{g ∈ B.pos} g` positive on the (unchanged) point set, and evaluates that
weight on `T`'s chain. -/
theorem ambCatX_good_pos {n m : ℕ} (X0 : SemiPf (n + (1 + m)))
    (T : Work.WilE9G.AmbStratum (n + (1 + m))) (B : Basic (n + (1 + m)) X0.r)
    (hTgood : T.Good) (hTB : ∀ z ∈ T.X.set, B.holds X0.c z) :
    (ambCatX T X0).Good ∧
    (∀ z ∈ (ambCatX T X0).X.set,
      0 < eaEval (ambCatX T X0).X.c (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) z) ∧
    (∀ z ∈ (ambCatX T X0).X.set,
      eaEval (ambCatX T X0).X.c (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) z
        = eaEval X0.c B.pos.prod z) := by
  refine ⟨(ambCatX_props T X0).2.1.mpr hTgood, ?_, ?_⟩
  · intro z hz
    rw [(ambCatX_props T X0).2.2.2.2.2.2.2 B.pos.prod z]
    exact prod_pos_of_holds X0 B (hTB z (by rw [← (ambCatX_props T X0).1]; exact hz))
  · intro z _
    exact (ambCatX_props T X0).2.2.2.2.2.2.2 B.pos.prod z

/-! ## Format and degree bookkeeping of the Lagrange stratum over `ambCatX` -/

/-- The value of `combineR` at `D`, as used to collapse the degree bookkeeping. -/
theorem combineR_eval (b5 : Polynomial ℕ) (D : ℕ) :
    2 * b5.eval D + D + 1 ≤ (combineR b5).eval D := by
  simp only [combineR, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- The format of the Lagrange stratum of `ambCatX T X0` is bounded by `a5 + 2 F + 2`, given that
`T` and `X0` have format bounded by `a5` and `F` respectively. -/
theorem ambCatX_lagStratumAE_fmt {n m F : ℕ} (X0 : SemiPf (n + (1 + m)))
    (T : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Psi : EAPoly (n + (1 + m)) X0.r) (c : Fin (1 + m) → ℝ) (a5 : ℕ)
    (hTfmt : T.X.fmt ≤ a5) (hX0r : X0.r ≤ F) (hTj : T.j ≤ F) :
    (Assembly.lagStratumAE (ambCatX T X0) (Work.WilE7.EAPoly.inr (r₁ := T.X.r) Psi) c).X.fmt
      ≤ a5 + 2 * F + 2 := by
  rw [Assembly.lagStratumAE_fmt, (ambCatX_props T X0).2.2.2.1, (ambCatX_props T X0).2.2.1]
  omega

/-- The degree of the Lagrange stratum of `ambCatX T X0` (with the lifted weight `Φ_B`) is bounded
by `b4` evaluated at `(combineR b5).eval D`. -/
theorem ambCatX_lagStratumAE_deg_bound {n m F : ℕ} (X0 : SemiPf (n + (1 + m)))
    (T : Work.WilE9G.AmbStratum (n + (1 + m))) (B : Basic (n + (1 + m)) X0.r)
    (c : Fin (1 + m) → ℝ) (b4 b5 : Polynomial ℕ) (a5 D : ℕ)
    (hTgood : T.Good) (hTne : T.X.set.Nonempty)
    (hTdeg : T.deg ≤ b5.eval B.deg) (hTlen : T.X.basics.length ≤ b5.eval B.deg)
    (hBdeg : B.deg ≤ X0.deg) (hX0deg : X0.deg ≤ D)
    (hTfmt : T.X.fmt ≤ a5) (hX0r : X0.r ≤ F)
    (hb4 : ∀ (S : Work.WilE9G.AmbStratum (n + (1 + m)))
      (Psi : EAPoly (n + (1 + m)) S.X.r) (c' : Fin (1 + m) → ℝ),
      S.j ≤ n + (1 + m) → S.X.fmt ≤ a5 + 2 * F + 2 →
      (Assembly.lagStratumAE S Psi c').deg ≤ b4.eval (S.deg + atomDeg Psi + S.X.basics.length)) :
    (Assembly.lagStratumAE (ambCatX T X0) (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) c).deg
      ≤ b4.eval ((combineR b5).eval D) := by
  have hSj : (ambCatX T X0).j ≤ n + (1 + m) := by
    rw [(ambCatX_props T X0).2.2.1]
    exact Assembly.ambStratum_j_le_ambient T hTgood hTne
  have hSfmt : (ambCatX T X0).X.fmt ≤ a5 + 2 * F + 2 := by
    rw [(ambCatX_props T X0).2.2.2.1]
    omega
  have hD : (ambCatX T X0).deg + atomDeg (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod)
      + (ambCatX T X0).X.basics.length ≤ (combineR b5).eval D := by
    rw [(ambCatX_props T X0).2.2.2.2.2.1, (ambCatX_props T X0).2.2.2.2.2.2.1]
    have h2 : atomDeg (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) ≤ B.deg + 1 := by
      rw [Work.WilE9.Ift.OneShot.atomDeg_inr]
      exact Assembly.atomDeg_pos_prod_le_basic B
    have h3 : b5.eval B.deg ≤ b5.eval D :=
      Assembly.poly_eval_mono b5 (le_trans hBdeg hX0deg)
    have h4 := combineR_eval b5 D
    omega
  exact (hb4 (ambCatX T X0) (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) c hSj hSfmt).trans
    (Assembly.poly_eval_mono b4 hD)

/-- The number of disjuncts of the Lagrange stratum of `ambCatX T X0` (with the lifted weight
`Φ_B`) is bounded by `masterPoly p2 b4 b5` evaluated at `D`. -/
theorem ambCatX_lagStratumAE_len_bound {n m : ℕ} (X0 : SemiPf (n + (1 + m)))
    (T : Work.WilE9G.AmbStratum (n + (1 + m))) (B : Basic (n + (1 + m)) X0.r)
    (c : Fin (1 + m) → ℝ) (b5 : Polynomial ℕ) (D : ℕ) (p2 b4 : Polynomial ℕ)
    (hTlen : T.X.basics.length ≤ b5.eval B.deg) (hBdeg : B.deg ≤ X0.deg)
    (hX0deg : X0.deg ≤ D) :
    (Assembly.lagStratumAE (ambCatX T X0)
        (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) c).X.basics.length
      ≤ (Assembly.masterPoly p2 b4 b5).eval D := by
  have h1 : (Assembly.lagStratumAE (ambCatX T X0)
        (Work.WilE7.EAPoly.inr (r₁ := T.X.r) B.pos.prod) c).X.basics.length
      = (ambCatX T X0).X.basics.length := by
    simp only [Assembly.lagStratumAE, List.length_map]
  have h2 : (ambCatX T X0).X.basics.length = T.X.basics.length :=
    (ambCatX_props T X0).2.2.2.2.2.2.1
  have h3 : b5.eval B.deg ≤ b5.eval D := Assembly.poly_eval_mono b5 (le_trans hBdeg hX0deg)
  have h4 : b5.eval D ≤ (b5 + Polynomial.C 1).eval D := by
    rw [(Assembly.masterPoly_bound p2 b4 b5 D).2.2.2.2.1]; exact Nat.le_succ _
  rw [h1, h2]
  exact le_trans hTlen (le_trans h3 (le_trans h4 (Assembly.masterPoly_bound p2 b4 b5 D).1))

end Work.WilE9G

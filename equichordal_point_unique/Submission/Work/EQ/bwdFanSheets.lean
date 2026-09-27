import Mathlib
import Submission.Work.EQ.bwdFanDefs

/-! # The local analytic sheets of the backward iterates of a stable fan

The labelled backward iterates `w ↦ bwdP a σ (fan a h ε w)` are not analytic (the principal
square root in `invBranch` jumps across its cut), but on the region where all the lower radicands
are non-zero their *multiset* is described by `2^i` locally analytic functions, built recursively
with the local analytic square roots `rootC`.  This module constructs those sheets and proves that
the product of all labelled radicands at levels `≤ n` is analytic at every point at which the
labelled radicands of levels `≤ n - 1` are non-zero. -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-! ## The two children of a backward step -/

/-- The child of `Q` in the direction `t`, using a chosen square root `ρ` of the radicand of `Q`:
`(-Q₁ + t(Q₁ + a/2)/ρ, -Q₂ + tQ₂/ρ)`.  With `t = ±1` and `ρ = brho (subO1 a Q)` this is
`invBranch a t Q`; with an analytic square root `ρ` it is the corresponding child in the analytic
sheet. -/
def bchild (a : ℝ) (t : ℂ) (ρ : ℂ) (Q : ℂ × ℂ) : ℂ × ℂ :=
  (-Q.1 + t * (Q.1 + ((a / 2 : ℝ) : ℂ)) / ρ, -Q.2 + t * Q.2 / ρ)

theorem invBranch_eq_bchild (a : ℝ) (t : Bool) (Q : ℂ × ℂ) :
    invBranch a t Q = bchild a (if t then (1 : ℂ) else -1) (brho (subO1 a Q)) Q := by
  simp only [invBranch, bchild, brho, bsq, subO1]

theorem bwdP_snoc_bchild (a : ℝ) (σ : List Bool) (t : Bool) (P : ℂ × ℂ) :
    bwdP a (σ ++ [t]) P =
      bchild a (if t then (1 : ℂ) else -1) (brho (subO1 a (bwdP a σ P))) (bwdP a σ P) := by
  rw [bwdP_snoc, invBranch_eq_bchild]

/-! ## The local analytic sheets -/

/-- The recursive sheet data at a base point `w₀`.  For a *reversed* word `τ` (so that the
recursion is structural), `sheetData τ = (u, s)` where `u` is the sheet point at the node `τ` and
`s` is a chosen local analytic square root of its radicand at `w₀`. -/
noncomputable def sheetData (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) :
    List Bool → (ℂ → ℂ × ℂ) × (ℂ → ℂ)
  | [] => (fan a h ε, rootC (fun u => bsq (subO1 a (fan a h ε u))) w₀)
  | t :: τ =>
      let p := sheetData a h ε w₀ τ
      let uu : ℂ → ℂ × ℂ := fun w => bchild a (if t then (1 : ℂ) else -1) (p.2 w) (p.1 w)
      (uu, rootC (fun w => bsq (subO1 a (uu w))) w₀)

/-- The sheet point at the sign list `σ` (indexed in the original orientation). -/
noncomputable def sheetU (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) (σ : List Bool) :
    ℂ → ℂ × ℂ :=
  (sheetData a h ε w₀ σ.reverse).1

/-- The chosen square root at the sign list `σ`. -/
noncomputable def sheetS (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) (σ : List Bool) : ℂ → ℂ :=
  (sheetData a h ε w₀ σ.reverse).2

@[simp] theorem sheetU_nil (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) :
    sheetU a h ε w₀ [] = fan a h ε := rfl

theorem sheetU_append (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) (τ : List Bool) (t : Bool) :
    sheetU a h ε w₀ (τ ++ [t]) =
      fun w => bchild a (if t then (1 : ℂ) else -1) (sheetS a h ε w₀ τ w)
        (sheetU a h ε w₀ τ w) := by
  simp only [sheetU, sheetS, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.append_nil]
  rfl

theorem sheetS_eq_rootC (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) (σ : List Bool) :
    sheetS a h ε w₀ σ =
      rootC (fun w => bsq (subO1 a (sheetU a h ε w₀ σ w))) w₀ := by
  rcases List.eq_nil_or_concat σ with rfl | ⟨L, b, rfl⟩
  · rfl
  · simp only [sheetU, sheetS, List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_nil]
    rfl

/-! ## Analyticity tools -/

theorem analyticAt_bsq_subO1 (a : ℝ) (Q : ℂ × ℂ) :
    AnalyticAt ℂ (fun Q : ℂ × ℂ => bsq (subO1 a Q)) Q := by
  have hfun : (fun Q : ℂ × ℂ => bsq (subO1 a Q)) =
      fun Q : ℂ × ℂ => (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 := by
    funext Q; simp [bsq, subO1]
  rw [hfun]
  exact ((analyticAt_fst.add analyticAt_const).pow 2).add (analyticAt_snd.pow 2)

theorem analyticAt_bsq_subO1_comp {a : ℝ} {P : ℂ → ℂ × ℂ} {z : ℂ}
    (hP : AnalyticAt ℂ P z) :
    AnalyticAt ℂ (fun w => bsq (subO1 a (P w))) z :=
  (analyticAt_bsq_subO1 a (P z)).comp hP

theorem analyticAt_bchild {a : ℝ} {P : ℂ → ℂ × ℂ} {s : ℂ → ℂ} {t : ℂ} {z : ℂ}
    (hP : AnalyticAt ℂ P z) (hs : AnalyticAt ℂ s z) (hs0 : s z ≠ 0) :
    AnalyticAt ℂ (fun w => bchild a t (s w) (P w)) z := by
  have h1 : AnalyticAt ℂ (fun w => (P w).1) z := analyticAt_fst.comp hP
  have h2 : AnalyticAt ℂ (fun w => (P w).2) z := analyticAt_snd.comp hP
  have hA : AnalyticAt ℂ (fun w =>
      -(P w).1 + t * ((P w).1 + ((a / 2 : ℝ) : ℂ)) / s w) z :=
    h1.neg.add ((analyticAt_const.mul (h1.add analyticAt_const)).div hs hs0)
  have hB : AnalyticAt ℂ (fun w => -(P w).2 + t * (P w).2 / s w) z :=
    h2.neg.add ((analyticAt_const.mul h2).div hs hs0)
  simpa only [bchild] using hA.prod hB

theorem analyticAt_list_prod {ι : Type*} {l : List ι} {F : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ x ∈ l, AnalyticAt ℂ (F x) z) :
    AnalyticAt ℂ (fun w => (l.map (fun x => F x w)).prod) z := by
  induction l with
  | nil =>
      simpa using (analyticAt_const (v := (1 : ℂ)) : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (h x (by simp)).mul (ih fun y hy => h y (by simp [hy]))

theorem analyticAt_sheetProd {a : ℝ} {U : List Bool → ℂ → ℂ × ℂ} {z : ℂ} {N : ℕ}
    (hu : ∀ σ, σ.length ≤ N → AnalyticAt ℂ (U σ) z) :
    AnalyticAt ℂ (fun w => sheetProd a N (fun σ => U σ w)) z := by
  unfold sheetProd
  refine analyticAt_list_prod fun i hi => ?_
  have hiN : i ≤ N := by
    have := List.mem_range.mp hi
    omega
  refine analyticAt_list_prod fun σ hσ => ?_
  have hlen : σ.length ≤ N := by
    have h2 : σ.length = i := mem_fanWords.mp hσ
    omega
  exact analyticAt_bsq_subO1_comp (hu σ hlen)

/-! ## The multiset of sheet points equals the multiset of labelled points -/

/-- If `s² = ρ²` then the two children computed with `s` are the two children computed with `ρ`,
just possibly in the other order. -/
theorem bchild_pair_perm {a : ℝ} {Q : ℂ × ℂ} {s ρ : ℂ} (h : s ^ 2 = ρ ^ 2) :
    List.Perm [bchild a 1 s Q, bchild a (-1) s Q] [bchild a 1 ρ Q, bchild a (-1) ρ Q] := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · rw [h]
  · subst h
    have h1 : bchild a 1 (-ρ) Q = bchild a (-1) ρ Q := by
      ext <;> simp only [bchild, one_mul] <;> ring_nf
    have h2 : bchild a (-1) (-ρ) Q = bchild a 1 ρ Q := by
      ext <;> simp only [bchild, one_mul] <;> ring_nf
    rw [h1, h2]
    exact List.Perm.swap _ _ _

/-- The multiset equality at level `0`. -/
theorem levelEq_zero (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ w : ℂ) :
    List.Perm ((fanWords 0).map (fun σ => sheetU a h ε w₀ σ w))
      ((fanWords 0).map (fun σ => bwdP a σ (fan a h ε w))) := by
  simp [fanWords]

/-- The multiset equality propagates one level up, using the square identity at level `j`. -/
theorem levelEq_succ (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (w₀ : ℂ) (j : ℕ)
    (hME : ∀ w, List.Perm ((fanWords j).map (fun σ => sheetU a h ε w₀ σ w))
      ((fanWords j).map (fun σ => bwdP a σ (fan a h ε w))))
    (hss : ∀ τ, τ.length = j → ∀ w, (sheetS a h ε w₀ τ w) ^ 2 =
      bsq (subO1 a (sheetU a h ε w₀ τ w))) :
    ∀ w, List.Perm ((fanWords (j + 1)).map (fun σ => sheetU a h ε w₀ σ w))
      ((fanWords (j + 1)).map (fun σ => bwdP a σ (fan a h ε w))) := by
  intro w
  -- the children of a point, as a two-element list
  set kids : ℂ × ℂ → List (ℂ × ℂ) :=
    fun Q => [bchild a 1 (brho (subO1 a Q)) Q, bchild a (-1) (brho (subO1 a Q)) Q]
  have hL : (fanWords (j + 1)).map (fun σ => sheetU a h ε w₀ σ w) =
      (fanWords j).flatMap (fun l =>
        [sheetU a h ε w₀ (l ++ [true]) w, sheetU a h ε w₀ (l ++ [false]) w]) := by
    rw [show fanWords (j + 1) = (fanWords j).flatMap
      (fun l => [l ++ [true], l ++ [false]]) from rfl, List.map_flatMap]
    simp
  have hR : (fanWords (j + 1)).map (fun σ => bwdP a σ (fan a h ε w)) =
      (fanWords j).flatMap (fun l =>
        [bwdP a (l ++ [true]) (fan a h ε w), bwdP a (l ++ [false]) (fan a h ε w)]) := by
    rw [show fanWords (j + 1) = (fanWords j).flatMap
      (fun l => [l ++ [true], l ++ [false]]) from rfl, List.map_flatMap]
    simp
  rw [hL, hR]
  -- the sheet children are the canonical children of the sheet points
  have hstep1 : List.Perm ((fanWords j).flatMap (fun l =>
        [sheetU a h ε w₀ (l ++ [true]) w, sheetU a h ε w₀ (l ++ [false]) w]))
      ((fanWords j).flatMap (fun l => kids (sheetU a h ε w₀ l w))) := by
    refine List.Perm.flatMap_left _ fun l hl => ?_
    have hlen : l.length = j := mem_fanWords.mp hl
    rw [sheetU_append, sheetU_append]
    exact bchild_pair_perm (by rw [hss l hlen w]; exact (brho_sq _).symm)
  refine hstep1.trans ?_
  -- reindex by the sheet values
  have hstep2 : (fanWords j).flatMap (fun l => kids (sheetU a h ε w₀ l w)) =
      ((fanWords j).map (fun l => sheetU a h ε w₀ l w)).flatMap kids := by
    rw [List.flatMap_map]
  rw [hstep2]
  refine (List.Perm.flatMap_right kids (hME w)).trans ?_
  -- reindex by the labelled values
  have hstep3 : ((fanWords j).map (fun l => bwdP a l (fan a h ε w))).flatMap kids =
      (fanWords j).flatMap (fun l =>
        [bwdP a (l ++ [true]) (fan a h ε w), bwdP a (l ++ [false]) (fan a h ε w)]) := by
    have h1 : ∀ l : List Bool,
        [bwdP a (l ++ [true]) (fan a h ε w), bwdP a (l ++ [false]) (fan a h ε w)] =
          kids (bwdP a l (fan a h ε w)) := by
      intro l
      rw [bwdP_snoc_bchild, bwdP_snoc_bchild]
      rfl
    simp only [h1]
    rw [List.flatMap_map]
  rw [hstep3]

/-! ## The analytic sheets -/

/-- A nonempty list is a prefix followed by one symbol. -/
theorem exists_append_singleton_of_length_eq_succ {τ : List Bool} {N : ℕ}
    (h : τ.length = N + 1) : ∃ L b, τ = L ++ [b] ∧ L.length = N := by
  rcases List.eq_nil_or_concat τ with hnil | ⟨L, b, hL⟩
  · rw [hnil] at h; simp at h
  · exact ⟨L, b, by rw [hL, List.concat_eq_append], by
      rw [hL] at h; simpa using h⟩

/-- **The sheet induction.**  If `fan a h τ` is analytic at `w₀` for every word `τ`, and every
labelled radicand of level `≤ n` is non-zero at `w₀`, then for every `N ≤ n + 1`:

* every sheet point of level `≤ N` is analytic at `w₀`;
* for every sign list of level `≤ min N n` the chosen root is analytic at `w₀`, non-zero there, and
  squares to the sheet radicand (pointwise);
* at every level `j ≤ N` the multiset of sheet points equals the multiset of labelled points. -/
theorem sheet_claim {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} {w₀ : ℂ} {n : ℕ}
    (hfan : ∀ τ : List Bool, AnalyticAt ℂ (fan a h τ) w₀)
    (hgood : ∀ σ : List Bool, σ.length ≤ n →
      bsq (subO1 a (bwdP a σ (fan a h ε w₀))) ≠ 0) :
    ∀ N ≤ n + 1,
      (∀ τ : List Bool, τ.length ≤ N → AnalyticAt ℂ (sheetU a h ε w₀ τ) w₀) ∧
      (∀ τ : List Bool, τ.length ≤ min N n → AnalyticAt ℂ (sheetS a h ε w₀ τ) w₀ ∧
        sheetS a h ε w₀ τ w₀ ≠ 0 ∧
        ∀ w, (sheetS a h ε w₀ τ w) ^ 2 = bsq (subO1 a (sheetU a h ε w₀ τ w))) ∧
      (∀ j ≤ N, ∀ w, List.Perm ((fanWords j).map (fun σ => sheetU a h ε w₀ σ w))
        ((fanWords j).map (fun σ => bwdP a σ (fan a h ε w)))) := by
  intro N
  induction N with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · intro τ hτ
        have hτ0 : τ.length = 0 := by omega
        rw [List.length_eq_zero_iff] at hτ0
        subst hτ0
        rw [sheetU_nil]
        exact hfan ε
      · intro τ hτ
        have hτ0 : τ = [] := by
          have : τ.length = 0 := by
            have h2 : τ.length ≤ min 0 n := hτ
            simpa using h2
          exact List.length_eq_zero_iff.mp this
        subst hτ0
        rw [sheetS_eq_rootC, sheetU_nil]
        exact rootC_spec (analyticAt_bsq_subO1_comp (a := a) (hfan ε)) (hgood [] (by simp))
      · intro j hj w
        have hj0 : j = 0 := by omega
        subst hj0
        exact levelEq_zero a h ε w₀ w
  | succ N ih =>
      intro hN
      have hNn : N ≤ n := Nat.le_of_succ_le_succ hN
      obtain ⟨IHA, IHB, IHC⟩ := ih (by omega : N ≤ n + 1)
      -- (a) analyticity of the sheet points up to level `N + 1`
      have hA : ∀ τ : List Bool, τ.length ≤ N + 1 → AnalyticAt ℂ (sheetU a h ε w₀ τ) w₀ := by
        intro τ hτ
        rcases le_or_gt τ.length N with hle | hgt
        · exact IHA τ hle
        · have hlen : τ.length = N + 1 := by omega
          obtain ⟨L, b, hτeq, hLlen⟩ := exists_append_singleton_of_length_eq_succ hlen
          rw [hτeq, sheetU_append]
          have hLB : L.length ≤ min N n := by rw [hLlen]; exact le_min le_rfl hNn
          exact analyticAt_bchild (IHA L (by omega)) (IHB L hLB).1 (IHB L hLB).2.1
      -- (c) the multiset equality up to level `N + 1`
      have hC : ∀ j ≤ N + 1, ∀ w, List.Perm ((fanWords j).map (fun σ => sheetU a h ε w₀ σ w))
          ((fanWords j).map (fun σ => bwdP a σ (fan a h ε w))) := by
        intro j hj w
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact IHC j (by omega) w
        · subst heq
          exact levelEq_succ a h ε w₀ N (fun w => IHC N le_rfl w)
            (fun τ hτ w => (IHB τ (by rw [hτ]; exact le_min le_rfl hNn)).2.2 w) w
      -- (b) the chosen roots up to level `min (N + 1) n`
      have hB : ∀ τ : List Bool, τ.length ≤ min (N + 1) n →
          AnalyticAt ℂ (sheetS a h ε w₀ τ) w₀ ∧ sheetS a h ε w₀ τ w₀ ≠ 0 ∧
            ∀ w, (sheetS a h ε w₀ τ w) ^ 2 = bsq (subO1 a (sheetU a h ε w₀ τ w)) := by
        intro τ hτ
        rcases le_or_gt τ.length N with hle | hgt
        · exact IHB τ (le_min hle (le_trans hτ (Nat.min_le_right _ _)))
        · have hlen : τ.length = N + 1 := by
            have h2 : τ.length ≤ N + 1 := le_trans hτ (Nat.min_le_left _ _)
            omega
          rw [sheetS_eq_rootC]
          refine rootC_spec (analyticAt_bsq_subO1_comp (hA τ (le_of_eq hlen))) ?_
          intro hzero
          -- the sheet radicand at level `τ.length` cannot vanish, by the multiset equality
          have hperm := (hC (N + 1) le_rfl w₀).map (fun Q : ℂ × ℂ => bsq (subO1 a Q))
          have hmem : (0 : ℂ) ∈ ((fanWords (N + 1)).map
              (fun σ => sheetU a h ε w₀ σ w₀)).map (fun Q => bsq (subO1 a Q)) := by
            refine List.mem_map.mpr ⟨sheetU a h ε w₀ τ w₀, ?_, hzero⟩
            exact List.mem_map.mpr ⟨τ, mem_fanWords.mpr hlen, rfl⟩
          have hmem2 : (0 : ℂ) ∈ ((fanWords (N + 1)).map
              (fun σ => bwdP a σ (fan a h ε w₀))).map (fun Q => bsq (subO1 a Q)) :=
            hperm.mem_iff.mp hmem
          obtain ⟨Q, hQ, hQz⟩ := List.mem_map.mp hmem2
          obtain ⟨σ, hσ, hσQ⟩ := List.mem_map.mp hQ
          have hσn : σ.length ≤ n := by
            have : σ.length = N + 1 := mem_fanWords.mp hσ
            omega
          exact hgood σ hσn (by rw [hσQ]; exact hQz)
      exact ⟨hA, hB, hC⟩

/-- Unfolding a product of a composed map. -/
theorem map_map_prod {ι : Type*} (l : List ι) (f : ι → ℂ × ℂ) (F : ℂ × ℂ → ℂ) :
    (l.map (fun a => F (f a))).prod = ((l.map f).map F).prod := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- **`bwdProd` is analytic at `w₀`**, provided the fan is analytic there and the labelled
radicands of levels `≤ n` do not vanish there. -/
theorem analyticAt_bwdProd_of_good {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} {w₀ : ℂ} {n : ℕ}
    (hfan : ∀ τ : List Bool, AnalyticAt ℂ (fan a h τ) w₀)
    (hgood : ∀ σ : List Bool, σ.length ≤ n →
      bsq (subO1 a (bwdP a σ (fan a h ε w₀))) ≠ 0) :
    AnalyticAt ℂ (bwdProd a h ε (n + 1)) w₀ := by
  obtain ⟨hA, -, hC⟩ := sheet_claim (a := a) (h := h) (ε := ε) (w₀ := w₀) (n := n) hfan hgood
    (n + 1) le_rfl
  have han : AnalyticAt ℂ (fun w => sheetProd a (n + 1) (fun σ => sheetU a h ε w₀ σ w)) w₀ :=
    analyticAt_sheetProd fun σ hσ => hA σ hσ
  have key : (fun w => sheetProd a (n + 1) (fun σ => sheetU a h ε w₀ σ w)) =ᶠ[𝓝 w₀]
      (bwdProd a h ε (n + 1)) := by
    refine Filter.Eventually.of_forall fun w => ?_
    have hinner : ∀ i ∈ List.range (n + 2),
        ((fanWords i).map (fun σ => bsq (subO1 a (sheetU a h ε w₀ σ w)))).prod =
          ((fanWords i).map (fun σ => bsq (subO1 a (bwdP a σ (fan a h ε w))))).prod := by
      intro i hi
      have hi' : i ≤ n + 1 := by
        have := List.mem_range.mp hi
        omega
      have hp := (hC i hi' w).map (fun Q : ℂ × ℂ => bsq (subO1 a Q))
      rw [map_map_prod (fanWords i) (fun σ => sheetU a h ε w₀ σ w) (fun Q => bsq (subO1 a Q)),
        map_map_prod (fanWords i) (fun σ => bwdP a σ (fan a h ε w)) (fun Q => bsq (subO1 a Q))]
      exact hp.prod_eq
    show ((List.range (n + 2)).map (fun i =>
          ((fanWords i).map (fun σ => bsq (subO1 a (sheetU a h ε w₀ σ w)))).prod)).prod
        = ((List.range (n + 2)).map (fun i =>
          ((fanWords i).map (fun σ => bsq (subO1 a (bwdP a σ (fan a h ε w))))).prod)).prod
    rw [List.map_congr_left hinner]
  exact han.congr key

end

end Work.EQ

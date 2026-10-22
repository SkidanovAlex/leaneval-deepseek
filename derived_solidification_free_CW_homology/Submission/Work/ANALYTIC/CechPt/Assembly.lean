import Submission.Work.ANALYTIC.CechPt.Plumbing

/-!
# Assembly of `level_acyclic`

This file proves the acyclicity of the cochain complex of the level-`n` dyadic nerve by strong
induction on the number `M` of vertices, using the prism identity (the homotopy
`d H + H d = rhoS^* - id`) to pass from level `M + 1` to level `M + 2`.
-/

namespace Work.ANALYTIC.CechPt.Level

/-! ## The alternating sum -/

/-- The alternating sum of `n` ones. -/
def altSum (n : ℕ) : ℤ := ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ)

theorem altSum_succ (n : ℕ) : altSum (n + 1) = 1 - altSum n := by
  have h : (∑ i : Fin n, (-1 : ℤ) ^ ((i : ℕ) + 1)) = -(∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [altSum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  rw [h, altSum]
  ring

theorem altSum_add_succ (n : ℕ) : altSum n + altSum (n + 1) = 1 := by
  induction n with
  | zero => simp [altSum]
  | succ n ih =>
    have h := altSum_succ n
    have h' := altSum_succ (n + 1)
    omega

theorem altSum_eq_zero_or_one (n : ℕ) : altSum n = 0 ∨ altSum n = 1 := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases n with _ | _ | m
  · left; simp [altSum]
  · right; simp [altSum]
  · have h := ih (m + 1) (by omega)
    have hs := altSum_succ (m + 1)
    rcases h with h | h <;> rw [hs, h] <;> norm_num

/-! ## Consequences of the prism identity -/

theorem H_zero {M : ℕ} (q : ℕ) : H q (fun _ : lev M (q + 1) => (0 : ℤ)) = 0 := by
  funext z
  show (∑ j : Fin (q + 1), (-1 : ℤ) ^ (j : ℕ) * (0 : ℤ)) = 0
  simp

/-- On cocycles, `H` is a primitive: `d (H q f) = f ∘ rhoS - f`. -/
theorem diff_H_eq (hid : ∀ {M : ℕ} (q : ℕ) (G : lev M (q + 1) → ℤ) (y : lev M (q + 1)),
      diff (H q G) y + H (q + 1) (diff G) y = G (rhoS y) - G y)
    {M : ℕ} {q : ℕ} {f : lev M (q + 1) → ℤ} (hf : diff f = 0) :
    diff (H q f) = fun y => f (rhoS y) - f y := by
  funext y
  have h1 := hid q f y
  have h2 : H (q + 1) (diff f) y = 0 := by
    rw [hf]
    simp [H]
  linarith

/-! ## The base cases -/

instance isEmpty_lev_zero (p : ℕ) : IsEmpty (lev 0 p) :=
  ⟨fun x => Fin.elim0 (x.1 0)⟩

theorem level_acyclic_prop_zero : level_acyclic_prop 0 := by
  constructor
  · intro p f _
    exact ⟨fun x => isEmptyElim x, by funext x; exact isEmptyElim x⟩
  · intro f _
    exact ⟨0, by funext x; exact isEmptyElim x⟩

instance subsingleton_lev_one (p : ℕ) : Subsingleton (lev 1 p) := by
  constructor
  intro a b
  apply Subtype.ext
  funext i
  apply Fin.ext
  have h1 := (a.1 i).isLt
  have h2 := (b.1 i).isLt
  omega

/-- The unique simplex of `lev 1 p`. -/
def pt1 (p : ℕ) : lev 1 p := ⟨fun _ => 0, by intro i j; simp only [Fin.le_def]; omega⟩

theorem level_acyclic_prop_one : level_acyclic_prop 1 := by
  constructor
  · intro p f hf
    have hdiff_const : ∀ (c : ℤ) (x : lev 1 (p + 1)),
        diff (fun _ : lev 1 p => c) x = c * altSum (p + 2) := by
      intro c x
      simp only [diff, altSum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hdiff_f : ∀ y : lev 1 (p + 2), diff f y = f (pt1 (p + 1)) * altSum (p + 3) := by
      intro y
      simp only [diff, altSum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Subsingleton.elim (face i y) (pt1 (p + 1))]
      ring
    by_cases hp : altSum (p + 2) = 1
    · refine ⟨fun _ => f (pt1 (p + 1)), ?_⟩
      funext x
      rw [hdiff_const, hp, mul_one]
      exact congrArg f (Subsingleton.elim (pt1 (p + 1)) x)
    · have h3 : altSum (p + 3) = 1 := by
        rcases altSum_eq_zero_or_one (p + 3) with h | h
        · have hsum := altSum_add_succ (p + 2)
          rw [show p + 2 + 1 = p + 3 from rfl] at hsum
          exact absurd (by omega : altSum (p + 2) = 1) hp
        · exact h
      have hf0 : f = fun _ => 0 := by
        funext x
        have hy := hdiff_f (pt1 (p + 2))
        rw [hf] at hy
        simp only [Pi.zero_apply, h3, mul_one] at hy
        rw [hy]
        exact congrArg f (Subsingleton.elim x (pt1 (p + 1)))
      refine ⟨fun _ => 0, ?_⟩
      funext x
      rw [hdiff_const, hf0]
      simp
  · intro f _
    refine ⟨f (pt1 0), ?_⟩
    funext x
    exact congrArg f (Subsingleton.elim x (pt1 0))

/-! ## The edge `(N, N+1)` -/

/-- The edge joining the vertices `N` and `N+1` in `lev (N+2) 1`. -/
def edgeS (N : ℕ) : lev (N + 2) 1 :=
  mkLev (fun i : Fin 2 => (if (i : ℕ) = 0 then (⟨N, by omega⟩ : Fin (N + 2))
      else (⟨N + 1, by omega⟩ : Fin (N + 2))))
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp <;> omega)

theorem face_edgeS_zero (N : ℕ) :
    face (0 : Fin 2) (edgeS N) = vtx (N + 2) ⟨N + 1, by omega⟩ := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  fin_cases i
  simp [face, edgeS, vtx, mkLev]

theorem face_edgeS_one (N : ℕ) :
    face (1 : Fin 2) (edgeS N) = vtx (N + 2) ⟨N, by omega⟩ := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  fin_cases i
  simp [face, edgeS, vtx, mkLev]

/-! ## The induction step -/

theorem level_acyclic_prop_all_of (hid : ∀ {M : ℕ} (q : ℕ) (G : lev M (q + 1) → ℤ)
      (y : lev M (q + 1)), diff (H q G) y + H (q + 1) (diff G) y = G (rhoS y) - G y) :
    ∀ M, level_acyclic_prop M := by
  intro M
  refine Nat.strong_induction_on M ?_
  intro M ih
  rcases M with _ | _ | N
  · exact level_acyclic_prop_zero
  · exact level_acyclic_prop_one
  · have ih' : level_acyclic_prop (N + 1) := ih (N + 1) (by omega)
    constructor
    · intro p f hf
      have hf' : diff (fun x : lev (N + 1) (p + 1) => f (inclS x)) = 0 := by
        rw [diff_inclS, hf]
        rfl
      obtain ⟨g', hg'⟩ := ih'.1 p (fun x => f (inclS x)) hf'
      have hG : diff (fun z : lev (N + 2) p => g' (retrS z)) = fun z => f (rhoS z) := by
        rw [diff_retrS, hg']
        funext z
        show f (inclS (retrS z)) = f (rhoS z)
        rw [inclS_retrS]
      have hH := diff_H_eq hid hf
      refine ⟨fun z => g' (retrS z) - H p f z, ?_⟩
      rw [diff_sub, hG, hH]
      funext y
      ring
    · intro f hf
      have hf' : diff (fun x : lev (N + 1) 0 => f (inclS x)) = 0 := by
        rw [diff_inclS, hf]
        rfl
      obtain ⟨c, hc⟩ := ih'.2 (fun x => f (inclS x)) hf'
      refine ⟨c, ?_⟩
      have hclamp : ∀ w : lev (N + 2) 0, f (rhoS w) = c := by
        intro w
        rw [← inclS_retrS w]
        exact congrFun hc (retrS w)
      have hfix : ∀ k : Fin (N + 2), (k : ℕ) ≤ N → f (vtx (N + 2) k) = c := by
        intro k hk
        have h1 : rhoS (vtx (N + 2) k) = vtx (N + 2) k := by
          rw [rhoS_vtx]
          congr 1
          apply Fin.ext
          simp only [rhoV]
          omega
        rw [← h1]
        exact hclamp (vtx (N + 2) k)
      have hedge : f (vtx (N + 2) ⟨N, by omega⟩) = f (vtx (N + 2) ⟨N + 1, by omega⟩) := by
        have h0 : diff f (edgeS N) = 0 := by rw [hf]; rfl
        rw [diff, Fin.sum_univ_two] at h0
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h0
        rw [face_edgeS_zero N, face_edgeS_one N] at h0
        linarith
      funext v
      rw [vtx_eta v]
      by_cases hv : ((v.1 0 : Fin (N + 2)) : ℕ) = N + 1
      · have h1 : vtx (N + 2) (v.1 0) = vtx (N + 2) ⟨N + 1, by omega⟩ := by
          congr 1
          exact Fin.ext hv
        rw [h1, ← hedge]
        exact hfix ⟨N, by omega⟩ (by show (N:ℕ) ≤ N; omega)
      · exact hfix (v.1 0) (by omega)

end Work.ANALYTIC.CechPt.Level

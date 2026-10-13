import Mathlib
import Submission.Work.WilE6.CritSA

namespace Work.WilE6

open WilkiesDesign WilkiesDesign.E

noncomputable section

variable {k r p : ℕ}

/-!
### Degree bound for the criterion set `critSA`

`critSA` has `k + 1` basic pieces, one for each attained sup-norm index `j : Fin (k+1)`.
This file shows that each piece has `deg` bounded uniformly in `j`.

The `Basic.deg` of a piece is the sum of the `atomDeg = totalDegree + 1` of its atoms
(equations and strict positivity conditions).  The books are:

* `k` atoms `atomMax i = u_i^2 - t^2 + wm_i^2` (degree `2`, atomDeg `3`) — `3*k`;
* one atom `atomJ j` (`= u_j^2 - t^2`, degree `2`) or `atomTz` (`= t`, degree `1`) — at most `3`;
* one atom `atomT0 = t - w0^2` (degree `2`, atomDeg `3`) — `3`;
* `2*p` atoms `atomWb = ±u - t^(κ^2) + wb^2`, of degree at most `κ^2 + 1` — `2*p*(κ^2+2)`;
* `2` atoms `atomWe = ±P - t^(κ^2) + we^2`, of degree at most `P.totalDegree + κ^2 + 1`
  — `2*(P.totalDegree + κ^2 + 2)`;
* `|Gs|` atoms `atomPos G = G - t^κ`, of degree at most `G.totalDegree + κ`
  — `Σ_G G.totalDegree + |Gs|*(κ+1)`.

The `3 + 3` of the second and third items are absorbed by the constant `8`.
-/

/-! ### `totalDegree` helpers -/

/-- The total degree of a difference is bounded by the maximum of the two total degrees. -/
theorem totalDegree_sub_le_max {σ : Type*} {R : Type*} [CommRing R]
    (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree := by
  calc (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ ≤ max a.totalDegree (-b).totalDegree := MvPolynomial.totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [MvPolynomial.totalDegree_neg]

theorem totalDegree_neg_le {σ : Type*} {R : Type*} [CommRing R] {a : MvPolynomial σ R} {n : ℕ}
    (h : a.totalDegree ≤ n) : (-a).totalDegree ≤ n := by
  rw [MvPolynomial.totalDegree_neg]; exact h

theorem totalDegree_sub_le_of {σ : Type*} {R : Type*} [CommRing R]
    {a b : MvPolynomial σ R} {n : ℕ} (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) :
    (a - b).totalDegree ≤ n :=
  (totalDegree_sub_le_max a b).trans (max_le ha hb)

theorem totalDegree_sub_add_le {σ : Type*} {R : Type*} [CommRing R]
    {a b c : MvPolynomial σ R} {n : ℕ}
    (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) (hc : c.totalDegree ≤ n) :
    (a - b + c).totalDegree ≤ n :=
  (MvPolynomial.totalDegree_add (a - b) c).trans
    (max_le ((totalDegree_sub_le_max a b).trans (max_le ha hb)) hc)

theorem totalDegree_ite_le {m : ℕ} {c : Prop} [Decidable c]
    {a b : MvPolynomial (Fin m) ℝ} {n : ℕ}
    (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) : (if c then a else b).totalDegree ≤ n := by
  split_ifs with h
  · exact ha
  · exact hb

theorem totalDegree_X_le {m : ℕ} (s : Fin m) :
    (MvPolynomial.X s : MvPolynomial (Fin m) ℝ).totalDegree ≤ 1 :=
  le_of_eq (MvPolynomial.totalDegree_X s)

theorem totalDegree_X_pow_le {m : ℕ} (s : Fin m) (n : ℕ) :
    ((MvPolynomial.X s : MvPolynomial (Fin m) ℝ) ^ n).totalDegree ≤ n := by
  calc _ ≤ n * (MvPolynomial.X s : MvPolynomial (Fin m) ℝ).totalDegree :=
        MvPolynomial.totalDegree_pow _ n
    _ = n := by rw [MvPolynomial.totalDegree_X, mul_one]

/-! ### Degrees of the atoms -/

theorem totalDegree_atomMax (i : Fin k) : (atomMax k r p i).totalDegree ≤ 2 := by
  simp only [atomMax]
  exact totalDegree_sub_add_le
    (totalDegree_X_pow_le (idxU k r p i) 2) (totalDegree_X_pow_le (idxT k r p) 2)
    (totalDegree_X_pow_le (idxWm k r p i) 2)

theorem totalDegree_atomT0 : (atomT0 k r p).totalDegree ≤ 2 := by
  simp only [atomT0]
  exact totalDegree_sub_le_of (le_trans (totalDegree_X_le (idxT k r p)) (by norm_num))
    (totalDegree_X_pow_le (idxW0 k r p) 2)

theorem totalDegree_atomJ (j : Fin k) : (atomJ k r p j).totalDegree ≤ 2 := by
  simp only [atomJ]
  exact totalDegree_sub_le_of (totalDegree_X_pow_le (idxU k r p j) 2)
    (totalDegree_X_pow_le (idxT k r p) 2)

theorem totalDegree_atomTz : (atomTz k r p).totalDegree ≤ 1 :=
  totalDegree_X_le (idxT k r p)

theorem totalDegree_polThr2 (κ : ℕ) : (polThr2 k r p κ).totalDegree ≤ κ ^ 2 :=
  totalDegree_X_pow_le (idxT k r p) (κ ^ 2)

theorem totalDegree_polThr1 (κ : ℕ) : (polThr1 k r p κ).totalDegree ≤ κ :=
  totalDegree_X_pow_le (idxT k r p) κ

theorem one_le_sq {κ : ℕ} (hκ : 1 ≤ κ) : 1 ≤ κ ^ 2 := Nat.one_le_pow 2 κ (by omega)

theorem totalDegree_atomWb (hp : p ≤ k) {κ : ℕ} (hκ : 1 ≤ κ) (j : Fin (2 * p)) :
    (atomWb k r p hp κ j).totalDegree ≤ κ ^ 2 + 1 := by
  have hκ2 : 1 ≤ κ ^ 2 := one_le_sq hκ
  simp only [atomWb]
  refine totalDegree_sub_add_le ?_ ?_ ?_
  · exact le_trans
      (totalDegree_ite_le (totalDegree_X_le (idxU k r p ⟨j.1 / 2, div2_lt hp j⟩))
        (totalDegree_neg_le (totalDegree_X_le (idxU k r p ⟨j.1 / 2, div2_lt hp j⟩))))
      (Nat.le_add_left 1 (κ ^ 2))
  · exact le_trans (totalDegree_polThr2 (k := k) (r := r) (p := p) κ) (Nat.le_add_right (κ ^ 2) 1)
  · exact le_trans (totalDegree_X_pow_le (idxWb k r p j) 2) (Nat.add_le_add_right hκ2 1)

theorem totalDegree_atomWe {κ : ℕ} (hκ : 1 ≤ κ)
    (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (j : Fin 2) :
    (atomWe k r p κ P j).totalDegree ≤ P.totalDegree + κ ^ 2 + 1 := by
  have hκ2 : 1 ≤ κ ^ 2 := one_le_sq hκ
  simp only [atomWe]
  refine totalDegree_sub_add_le ?_ ?_ ?_
  · exact le_trans
      (totalDegree_ite_le (MvPolynomial.totalDegree_rename_le (idxPhi k r p) P)
        (totalDegree_neg_le (MvPolynomial.totalDegree_rename_le (idxPhi k r p) P)))
      (Nat.le_add_right P.totalDegree (κ ^ 2 + 1))
  · exact le_trans (totalDegree_polThr2 (k := k) (r := r) (p := p) κ) (by omega)
  · exact le_trans (totalDegree_X_pow_le (idxWe k r p j) 2) (by omega)

theorem totalDegree_atomPos (κ : ℕ) (G : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) :
    (atomPos k r p κ G).totalDegree ≤ G.totalDegree + κ := by
  simp only [atomPos]
  refine totalDegree_sub_le_of ?_ ?_
  · exact le_trans (MvPolynomial.totalDegree_rename_le (idxPhi k r p) G)
      (Nat.le_add_right G.totalDegree κ)
  · exact le_trans (totalDegree_polThr1 (k := k) (r := r) (p := p) κ)
      (Nat.le_add_left κ G.totalDegree)

/-! ### `atomDeg` of a transported polynomial, and sums over lists -/

theorem atomDeg_saPoly_le {m : ℕ} {Q : MvPolynomial (Fin m) ℝ} {c : ℕ}
    (h : Q.totalDegree ≤ c) : atomDeg (saPoly m Q) ≤ c + 1 := by
  rw [atomDeg_saPoly, degP]
  exact Nat.add_le_add_right h 1

theorem sum_map_degP_le {m : ℕ} {L : List (MvPolynomial (Fin m) ℝ)} {c : ℕ}
    (h : ∀ P ∈ L, P.totalDegree ≤ c) : (L.map degP).sum ≤ L.length * (c + 1) := by
  have h2 : ∀ Q ∈ L.map degP, Q ≤ c + 1 := by
    intro Q hQ
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
    exact Nat.add_le_add_right (h P hP) 1
  have := List.sum_le_length_nsmul (L.map degP) (c + 1) h2
  simpa [nsmul_eq_mul] using this

theorem sum_map_atomDeg_saPoly_le {m : ℕ} {α : Type*} {L : List α}
    {f : α → MvPolynomial (Fin m) ℝ} {c : ℕ}
    (h : ∀ a ∈ L, (f a).totalDegree ≤ c) :
    ((L.map (fun a => saPoly m (f a))).map atomDeg).sum ≤ L.length * (c + 1) := by
  rw [List.map_map]
  have h2 : ∀ Q ∈ L.map (atomDeg ∘ fun a => saPoly m (f a)), Q ≤ c + 1 := by
    intro Q hQ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hQ
    exact atomDeg_saPoly_le (h a ha)
  have := List.sum_le_length_nsmul (L.map (atomDeg ∘ fun a => saPoly m (f a))) (c + 1) h2
  simpa [nsmul_eq_mul] using this

theorem sum_append5_le {m : ℕ} {L1 L2 L3 L4 L5 : List (EAPoly m 0)} {b1 b2 b3 b4 b5 : ℕ}
    (h1 : (L1.map atomDeg).sum ≤ b1) (h2 : (L2.map atomDeg).sum ≤ b2)
    (h3 : (L3.map atomDeg).sum ≤ b3) (h4 : (L4.map atomDeg).sum ≤ b4)
    (h5 : (L5.map atomDeg).sum ≤ b5) :
    ((L1 ++ L2 ++ L3 ++ L4 ++ L5).map atomDeg).sum ≤ b1 + b2 + b3 + b4 + b5 := by
  simp only [List.map_append, List.sum_append]
  omega

theorem sum_map_const {α : Type*} (L : List α) (c : ℕ) :
    (L.map (fun _ => c)).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem sum_map_atomDeg_singleton {m : ℕ} (x : EAPoly m 0) :
    (([x].map atomDeg)).sum = atomDeg x := by
  simp

/-! ### The list of equations of a piece -/

/-- The list of equations (`= 0`-atoms) of the `j`-th basic piece of `critSA`, transported into
`EAPoly (BP k r + FQ k p) 0`, in the same order as in `critBasic`. -/
def critEqs (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (j : Fin (k + 1)) :
    List (EAPoly (BP k r + FQ k p) 0) :=
  (List.finRange k).map (fun i => saPoly _ (atomMax k r p i)) ++
    (if h : (j : ℕ) < k then [saPoly _ (atomJ k r p ⟨j, h⟩)] else [saPoly _ (atomTz k r p)]) ++
    [saPoly _ (atomT0 k r p)] ++
    (List.finRange (2 * p)).map (fun i => saPoly _ (atomWb k r p hp κ i)) ++
    (List.finRange 2).map (fun i => saPoly _ (atomWe k r p κ P i))

theorem critBasic_eq (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (j : Fin (k + 1)) :
    critBasic (p := p) hp κ P Gs j =
      ⟨critEqs (p := p) hp κ P j,
        Gs.map (fun G => saPoly _ (atomPos k r p κ G))⟩ := rfl

theorem basic_deg_mk {m : ℕ} (eqs pos : List (EAPoly m 0)) :
    (⟨eqs, pos⟩ : Basic m 0).deg = (eqs.map atomDeg).sum + (pos.map atomDeg).sum := by
  simp [Basic.deg, List.map_append, List.sum_append]

/-! ### Bounds for the pieces -/

theorem critEqs_deg_le (hp : p ≤ k) {κ : ℕ} (hκ : 1 ≤ κ)
    (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (j : Fin (k + 1)) :
    ((critEqs (p := p) hp κ P j).map atomDeg).sum ≤
      3 * k + 6 + 2 * p * (κ ^ 2 + 2) + 2 * (P.totalDegree + κ ^ 2 + 2) := by
  have hP1 : (((List.finRange k).map
      (fun i => saPoly (BP k r + FQ k p) (atomMax k r p i))).map atomDeg).sum ≤ 3 * k := by
    have h := sum_map_atomDeg_saPoly_le (m := BP k r + FQ k p) (L := List.finRange k)
      (f := atomMax k r p) (c := 2)
      (by intro i _; exact totalDegree_atomMax (k := k) (r := r) (p := p) i)
    simp only [List.length_finRange] at h
    omega
  have hP2 : (((if h : (j : ℕ) < k then [saPoly (BP k r + FQ k p) (atomJ k r p ⟨j, h⟩)]
      else [saPoly (BP k r + FQ k p) (atomTz k r p)]).map atomDeg)).sum ≤ 3 := by
    split_ifs with h
    · rw [sum_map_atomDeg_singleton]
      exact le_trans (atomDeg_saPoly_le (totalDegree_atomJ (k := k) (r := r) (p := p) ⟨j, h⟩))
        (by norm_num)
    · rw [sum_map_atomDeg_singleton]
      exact le_trans
        (atomDeg_saPoly_le (totalDegree_atomTz (k := k) (r := r) (p := p))) (by norm_num)
  have hP3 : ((([saPoly (BP k r + FQ k p) (atomT0 k r p)]).map atomDeg)).sum ≤ 3 := by
    rw [sum_map_atomDeg_singleton]
    exact le_trans (atomDeg_saPoly_le (totalDegree_atomT0 (k := k) (r := r) (p := p)))
      (by norm_num)
  have hP4 : (((List.finRange (2 * p)).map
      (fun i => saPoly (BP k r + FQ k p) (atomWb k r p hp κ i))).map atomDeg).sum
      ≤ 2 * p * (κ ^ 2 + 2) := by
    have h := sum_map_atomDeg_saPoly_le (m := BP k r + FQ k p) (L := List.finRange (2 * p))
      (f := atomWb k r p hp κ) (c := κ ^ 2 + 1)
      (by intro i _; exact totalDegree_atomWb hp hκ i)
    simpa only [List.length_finRange] using h
  have hP5 : (((List.finRange 2).map
      (fun i => saPoly (BP k r + FQ k p) (atomWe k r p κ P i))).map atomDeg).sum
      ≤ 2 * (P.totalDegree + κ ^ 2 + 2) := by
    have h := sum_map_atomDeg_saPoly_le (m := BP k r + FQ k p) (L := List.finRange 2)
      (f := atomWe k r p κ P) (c := P.totalDegree + κ ^ 2 + 1)
      (by intro i _; exact totalDegree_atomWe hκ P i)
    simpa only [List.length_finRange] using h
  rw [critEqs]
  refine le_trans (sum_append5_le hP1 hP2 hP3 hP4 hP5) ?_
  omega

theorem critPos_deg_le {κ : ℕ}
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) :
    ((Gs.map (fun G => saPoly (BP k r + FQ k p) (atomPos k r p κ G))).map atomDeg).sum ≤
      (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1) := by
  calc ((Gs.map (fun G => saPoly (BP k r + FQ k p) (atomPos k r p κ G))).map atomDeg).sum
      = (Gs.map (fun G => degP (atomPos k r p κ G))).sum := by
        simp only [List.map_map, Function.comp_def, atomDeg_saPoly]
    _ ≤ (Gs.map (fun G => G.totalDegree + κ + 1)).sum := by
        apply List.sum_le_sum
        intro G _
        exact Nat.add_le_add_right (totalDegree_atomPos (k := k) (r := r) (p := p) κ G) 1
    _ = (Gs.map (fun G => G.totalDegree + (κ + 1))).sum := by simp only [Nat.add_assoc]
    _ = (Gs.map (fun G => G.totalDegree)).sum + (Gs.map (fun _ => κ + 1)).sum := by
        rw [List.sum_map_add]
    _ = (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1) := by
        rw [sum_map_const]

theorem critBasic_deg_le (hp : p ≤ k) {κ : ℕ} (hκ : 1 ≤ κ)
    (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (j : Fin (k + 1)) :
    (critBasic (p := p) hp κ P Gs j).deg ≤
      3 * k + 8 + 2 * p * (κ ^ 2 + 2) + 2 * (P.totalDegree + κ ^ 2 + 2)
        + (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1) := by
  have hEqs := critEqs_deg_le (p := p) hp hκ P j
  have hPos := critPos_deg_le (p := p) (k := k) (r := r) (κ := κ) Gs
  rw [critBasic_eq (p := p) hp κ P Gs j, basic_deg_mk]
  refine le_trans (add_le_add hEqs hPos) ?_
  omega

theorem critSA_deg_le {k r p : ℕ} (hp : p ≤ k) (κ : ℕ) (hκ : 1 ≤ κ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) : (Work.WilE6.critSA (p := p) hp κ P Gs).deg ≤ (k + 1) * (3 * k + 8 + 2 * p * (κ ^ 2 + 2) + 2 * (P.totalDegree + κ ^ 2 + 2) + (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1)) := by
  have hpiece : ∀ j ∈ List.finRange (k + 1),
      (critBasic (p := p) hp κ P Gs j).deg ≤
        3 * k + 8 + 2 * p * (κ ^ 2 + 2) + 2 * (P.totalDegree + κ ^ 2 + 2)
          + (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1) :=
    fun j _ => critBasic_deg_le (p := p) hp hκ P Gs j
  have hdeg : (Work.WilE6.critSA (p := p) hp κ P Gs).deg =
      (((List.finRange (k + 1)).map (critBasic (p := p) hp κ P Gs)).map Basic.deg).sum := rfl
  rw [hdeg]
  calc (((List.finRange (k + 1)).map (critBasic (p := p) hp κ P Gs)).map Basic.deg).sum
      = ((List.finRange (k + 1)).map
          (fun j => (critBasic (p := p) hp κ P Gs j).deg)).sum := by
        rw [List.map_map]; rfl
    _ ≤ ((List.finRange (k + 1)).map (fun _ =>
          (3 * k + 8 + 2 * p * (κ ^ 2 + 2) + 2 * (P.totalDegree + κ ^ 2 + 2)
            + (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1)))).sum := by
        apply List.sum_le_sum
        intro j _
        exact hpiece j (List.mem_finRange j)
    _ = (k + 1) * (3 * k + 8 + 2 * p * (κ ^ 2 + 2) + 2 * (P.totalDegree + κ ^ 2 + 2)
          + (Gs.map (fun G => G.totalDegree)).sum + Gs.length * (κ + 1)) := by
        rw [sum_map_const, List.length_finRange]

end

end Work.WilE6

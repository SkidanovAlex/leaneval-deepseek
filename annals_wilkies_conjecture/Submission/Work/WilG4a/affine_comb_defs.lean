/-
  WilG4a : vocabulary and helpers for the lemma `affine_comb_graph_mem`.

  Given two `Ω`-definable graphs `graphOf lo`, `graphOf hi ⊆ ℝ^{p+1}`, we want the graph of
  the affine combination `l ↦ c₁ + c₂ * lo l + c₃ * hi l` to be `Ω`-definable with a
  format/degree depending only on the inputs.

  The construction works in `ℝ^{p+3}`, coordinates indexed by `Fin (p+3)`:

    * `0, …, p-1`   — the `p` parameters `x`;
    * `yIdx p = p`   — the output value `y`;
    * `uIdx p = p+1` — a copy of `lo x`;
    * `vIdx p = p+2` — a copy of `hi x`.

  `lift2 A` places a set `A ⊆ ℝ^{p+1}` on the first `p+1` coordinates of `ℝ^{p+3}` (the shape
  produced by two applications of `SOMin.prod_right`), while `sigA p`, `sigB p` are the
  reindexings of `Fin (p+3)` that read `(x, u)` resp. `(x, v)` as the first `p+1`
  coordinates.  Membership in `SA p A = {x | x ∘ sigA p ∈ lift2 A}` is therefore
  "`(parameters x, x (uIdx p)) ∈ A`", and the `Ω`-membership of `SA` follows from the
  *balanced reindexing* `Work.WilG5.reindex_mem` applied to `lift2_mem`.

  With this, the graph of the affine combination is the projection along the last two
  coordinates of `SA p (graphOf lo) ∩ SB p (graphOf hi) ∩ Seq p c₁ c₂ c₃`, where `Seq` codes
  the affine relation `y = c₁ + c₂ * u + c₃ * v`.
-/
import Mathlib
import Submission.Work.WilG5.Reindex

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesDesign

/-! ## The ambient coordinates -/

/-- The output/value coordinate `⟨p⟩` of `Fin (p+3)`, written as the first coordinate after
the `p+1` coordinates of the lifted set. -/
def yIdx (p : ℕ) : Fin (p+3) := Fin.castAdd 2 (Fin.last p)

/-- The coordinate `⟨p+1⟩` of `Fin (p+3)`: where `lo`'s value is recorded. -/
def uIdx (p : ℕ) : Fin (p+3) := Fin.natAdd (p+1) (0 : Fin 2)

/-- The coordinate `⟨p+2⟩` of `Fin (p+3)`: where `hi`'s value is recorded. -/
def vIdx (p : ℕ) : Fin (p+3) := Fin.natAdd (p+1) (1 : Fin 2)

/-! ## Lifting and reindexing -/

/-- A set `A ⊆ ℝ^{p+1}` placed on the first `p+1` coordinates of `ℝ^{p+3}`. -/
def lift2 {p : ℕ} (A : Set (Fin (p+1) → ℝ)) : Set (Fin (p+3) → ℝ) :=
  {z | Fin.init (Fin.init z) ∈ A}

/-- `lift2` is `Ω`-definable whenever `A` is (two applications of `SOMin.prod_right`). -/
theorem lift2_mem {S : SOMin} {p F D : ℕ} {A : Set (Fin (p+1) → ℝ)}
    (hA : A ∈ S.Ω F D (p+1)) : lift2 A ∈ S.Ω (F + 2) D (p+3) :=
  S.prod_right (S.prod_right hA)

/-- Reindexing of `Fin (p+3)`: coordinates `0, …, p-1` are kept, coordinate `p` is sent to
`uIdx p = p+1` (the remaining coordinates are irrelevant for `lift2`). -/
def sigA (p : ℕ) : Fin (p+3) → Fin (p+3) :=
  fun j => if j.val < p then j else uIdx p

/-- Reindexing of `Fin (p+3)`: coordinates `0, …, p-1` are kept, coordinate `p` is sent to
`vIdx p = p+2`. -/
def sigB (p : ℕ) : Fin (p+3) → Fin (p+3) :=
  fun j => if j.val < p then j else vIdx p

/-- The set "`(parameters x, x (uIdx p)) ∈ A`" inside `ℝ^{p+3}`. -/
def SA (p : ℕ) (A : Set (Fin (p+1) → ℝ)) : Set (Fin (p+3) → ℝ) :=
  {x | x ∘ sigA p ∈ lift2 A}

/-- The set "`(parameters x, x (vIdx p)) ∈ B`" inside `ℝ^{p+3}`. -/
def SB (p : ℕ) (B : Set (Fin (p+1) → ℝ)) : Set (Fin (p+3) → ℝ) :=
  {x | x ∘ sigB p ∈ lift2 B}

/-- The affine relation `z (yIdx p) = c₁ + c₂ * z (uIdx p) + c₃ * z (vIdx p)`. -/
def Seq (p : ℕ) (c₁ c₂ c₃ : ℝ) : Set (Fin (p+3) → ℝ) :=
  {z | z (yIdx p) = c₁ + c₂ * z (uIdx p) + c₃ * z (vIdx p)}

theorem sigA_of_lt (p : ℕ) {j : Fin (p+3)} (h : j.val < p) : sigA p j = j := by
  unfold sigA
  rw [if_pos h]

theorem sigA_of_not_lt (p : ℕ) {j : Fin (p+3)} (h : ¬ j.val < p) : sigA p j = uIdx p := by
  unfold sigA
  rw [if_neg h]

theorem sigB_of_lt (p : ℕ) {j : Fin (p+3)} (h : j.val < p) : sigB p j = j := by
  unfold sigB
  rw [if_pos h]

theorem sigB_of_not_lt (p : ℕ) {j : Fin (p+3)} (h : ¬ j.val < p) : sigB p j = vIdx p := by
  unfold sigB
  rw [if_neg h]

/-! ## The format and degree bookkeeping -/

/-- The format obtained from two balanced reindexings of a `lift2` of a set of format `F`. -/
def omegaFmt (p F : ℕ) : ℕ :=
  max (F + 2 + (p + 3)) (4 * ((p + 3) + (p + 3)) + 8) + 1 + (p + 3)

/-- The degree obtained from two balanced reindexings. -/
def omegaDeg (p D : ℕ) : ℕ := D + (2 * (p + 3) + 4)

/-- The polynomial bounding the format/degree in `affine_comb_graph_mem`: it evaluates to
`2 * D + (4 * (p + 3) + 9)`, which dominates the degrees produced by the two reindexings, the
intersection and the projection. -/
def bpoly (p : ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.C (4 * (p + 3) + 9) + MvPolynomial.C 2 * MvPolynomial.X (0 : Fin 2)

theorem bpoly_eval (p D r : ℕ) :
    MvPolynomial.eval ![D, r] (bpoly p) = 2 * D + (4 * (p + 3) + 9) := by
  simp [bpoly]
  try omega

/-! ## `Ω`-membership of the three pieces -/

/-- `Ω`-membership of the reindexed `lo`-graph piece, with the explicit bounds
`omegaFmt p F` and `omegaDeg p D`. -/
theorem SA_mem {S : SOMin} {p F D : ℕ} {A : Set (Fin (p+1) → ℝ)}
    (hA : A ∈ S.Ω F D (p+1)) : SA p A ∈ S.Ω (omegaFmt p F) (omegaDeg p D) (p+3) := by
  have h := Work.WilG5.reindex_mem (S := S) (sigA p) (lift2_mem (S := S) hA)
  simpa only [SA, omegaFmt, omegaDeg] using h

/-- `Ω`-membership of the reindexed `hi`-graph piece. -/
theorem SB_mem {S : SOMin} {p F D : ℕ} {B : Set (Fin (p+1) → ℝ)}
    (hB : B ∈ S.Ω F D (p+1)) : SB p B ∈ S.Ω (omegaFmt p F) (omegaDeg p D) (p+3) := by
  have h := Work.WilG5.reindex_mem (S := S) (sigB p) (lift2_mem (S := S) hB)
  simpa only [SB, omegaFmt, omegaDeg] using h

/-- The linear polynomial whose zero set is `Seq`. -/
def seqPoly (p : ℕ) (c₁ c₂ c₃ : ℝ) : MvPolynomial (Fin (p+3)) ℝ :=
  MvPolynomial.X (yIdx p) - MvPolynomial.C c₁ -
    (MvPolynomial.C c₂ * MvPolynomial.X (uIdx p) + MvPolynomial.C c₃ * MvPolynomial.X (vIdx p))

theorem seqPoly_eval (p : ℕ) (c₁ c₂ c₃ : ℝ) (z : Fin (p+3) → ℝ) :
    MvPolynomial.eval z (seqPoly p c₁ c₂ c₃) =
      z (yIdx p) - c₁ - (c₂ * z (uIdx p) + c₃ * z (vIdx p)) := by
  simp [seqPoly]

theorem seqPoly_set (p : ℕ) (c₁ c₂ c₃ : ℝ) :
    {x : Fin (p+3) → ℝ | MvPolynomial.eval x (seqPoly p c₁ c₂ c₃) = 0} = Seq p c₁ c₂ c₃ := by
  ext z
  simp only [Set.mem_ofPred_eq, Seq]
  rw [seqPoly_eval]
  constructor <;> intro h <;> linarith

theorem seqPoly_totalDegree_le (p : ℕ) (c₁ c₂ c₃ : ℝ) :
    (seqPoly p c₁ c₂ c₃).totalDegree ≤ 1 := by
  have h1 : (MvPolynomial.X (yIdx p) - MvPolynomial.C c₁ :
      MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 1 :=
    Work.WilG5.td_X_sub_C_le (yIdx p) c₁
  have h2 : (MvPolynomial.C c₂ * MvPolynomial.X (uIdx p) :
      MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have hc : (MvPolynomial.C c₂ : MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 0 :=
      Work.WilG5.td_C_le c₂
    have hx : (MvPolynomial.X (uIdx p) : MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 1 :=
      Work.WilG5.td_X_le _
    omega
  have h3 : (MvPolynomial.C c₃ * MvPolynomial.X (vIdx p) :
      MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have hc : (MvPolynomial.C c₃ : MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 0 :=
      Work.WilG5.td_C_le c₃
    have hx : (MvPolynomial.X (vIdx p) : MvPolynomial (Fin (p+3)) ℝ).totalDegree ≤ 1 :=
      Work.WilG5.td_X_le _
    omega
  have h4 : ((MvPolynomial.C c₂ * MvPolynomial.X (uIdx p) +
      MvPolynomial.C c₃ * MvPolynomial.X (vIdx p) :
      MvPolynomial (Fin (p+3)) ℝ)).totalDegree ≤ 1 :=
    le_trans (MvPolynomial.totalDegree_add _ _) (max_le h2 h3)
  exact le_trans (Work.WilG5.td_sub_le _ _) (max_le h1 h4)

/-- `Ω`-membership of the affine relation set `Seq`, at the format `omegaFmt p F`. -/
theorem Seq_mem {S : SOMin} (p : ℕ) (F : ℕ) (c₁ c₂ c₃ : ℝ) :
    Seq p c₁ c₂ c₃ ∈ S.Ω (omegaFmt p F) 1 (p+3) := by
  have h := S.hyp (p+3) (seqPoly p c₁ c₂ c₃)
  rw [seqPoly_set] at h
  refine Work.WilG5.mem_mono h (omegaFmt p F) 1 ?_ (seqPoly_totalDegree_le p c₁ c₂ c₃)
  exact le_add_of_nonneg_left (Nat.zero_le _)

/-! ## Binary intersection helpers -/

theorem iInter_fin_two_ac {α : Type*} (A : Fin 2 → Set α) : (⋂ i, A i) = A 0 ∩ A 1 := by
  ext z
  simp [Set.mem_iInter]

theorem sum_fin_two_nat (D1 D2 : ℕ) : (∑ i : Fin 2, ![D1, D2] i) = D1 + D2 := by
  simp [Fin.sum_univ_two]

/-- `SOMin.inter` in the binary case, with the two sets at the same format. -/
theorem inter_mem {S : SOMin} {n : ℕ} {F D1 D2 : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D1 n) (hB : B ∈ S.Ω F D2 n) : A ∩ B ∈ S.Ω (F + 1) (D1 + D2) n := by
  have h : ∀ i : Fin 2, (![A, B] i) ∈ S.Ω F (![D1, D2] i) n := by
    intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
  have hmain := S.inter ![D1, D2] ![A, B] h
  rw [iInter_fin_two_ac] at hmain
  rw [sum_fin_two_nat] at hmain
  exact hmain

/-! ## Index computations for `Fin.append` -/

@[simp] theorem append_uIdx (p : ℕ) (x : Fin (p+1) → ℝ) (w : Fin 2 → ℝ) :
    Fin.append x w (uIdx p) = w 0 :=
  Fin.append_right x w 0

@[simp] theorem append_vIdx (p : ℕ) (x : Fin (p+1) → ℝ) (w : Fin 2 → ℝ) :
    Fin.append x w (vIdx p) = w 1 :=
  Fin.append_right x w 1

@[simp] theorem append_yIdx (p : ℕ) (x : Fin (p+1) → ℝ) (w : Fin 2 → ℝ) :
    Fin.append x w (yIdx p) = x (Fin.last p) :=
  Fin.append_left x w (Fin.last p)

theorem init3_append (p : ℕ) (x : Fin (p+1) → ℝ) (w : Fin 2 → ℝ) :
    Fin.init (Fin.init (Fin.init (Fin.append (m := p+1) (n := 2) x w))) = Fin.init x := by
  funext i
  show Fin.append (m := p+1) (n := 2) x w
      (Fin.castSucc (Fin.castSucc (Fin.castSucc i))) = x (Fin.castSucc i)
  rw [show (Fin.castSucc (Fin.castSucc (Fin.castSucc i)) : Fin (p+3)) =
        Fin.castAdd 2 (Fin.castSucc i) from Fin.ext rfl]
  exact Fin.append_left x w (Fin.castSucc i)

/-! ## The two graph characterisations -/

/-- Membership in `SA p (graphOf lo)`: the `u`-coordinate is `lo` of the parameters. -/
theorem sa_char (p : ℕ) (lo : (Fin p → ℝ) → ℝ) :
    SA p (graphOf lo) =
      {x : Fin (p+3) → ℝ | x (uIdx p) = lo (Fin.init (Fin.init (Fin.init x)))} := by
  ext x
  have hvec : Fin.init (Fin.init (x ∘ sigA p)) =
      Fin.snoc (Fin.init (Fin.init (Fin.init x))) (x (uIdx p)) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      show x (sigA p (Fin.castSucc (Fin.castSucc (Fin.last p)))) = x (uIdx p)
      rw [sigA_of_not_lt p (by simp)]
    · intro j
      rw [Fin.snoc_castSucc]
      show x (sigA p (Fin.castSucc (Fin.castSucc (Fin.castSucc j)))) =
        x (Fin.castSucc (Fin.castSucc (Fin.castSucc j)))
      rw [sigA_of_lt p (by exact j.isLt)]
  have hfun : Fin.init (Fin.init (Fin.init (x ∘ sigA p))) =
      Fin.init (Fin.init (Fin.init x)) := by
    rw [hvec, Fin.init_snoc]
  simp only [SA, lift2, Set.mem_ofPred_eq, graphOf]
  rw [hfun, hvec, Fin.snoc_last]

/-- Membership in `SB p (graphOf hi)`: the `v`-coordinate is `hi` of the parameters. -/
theorem sb_char (p : ℕ) (hi : (Fin p → ℝ) → ℝ) :
    SB p (graphOf hi) =
      {x : Fin (p+3) → ℝ | x (vIdx p) = hi (Fin.init (Fin.init (Fin.init x)))} := by
  ext x
  have hvec : Fin.init (Fin.init (x ∘ sigB p)) =
      Fin.snoc (Fin.init (Fin.init (Fin.init x))) (x (vIdx p)) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      show x (sigB p (Fin.castSucc (Fin.castSucc (Fin.last p)))) = x (vIdx p)
      rw [sigB_of_not_lt p (by simp)]
    · intro j
      rw [Fin.snoc_castSucc]
      show x (sigB p (Fin.castSucc (Fin.castSucc (Fin.castSucc j)))) =
        x (Fin.castSucc (Fin.castSucc (Fin.castSucc j)))
      rw [sigB_of_lt p (by exact j.isLt)]
  have hfun : Fin.init (Fin.init (Fin.init (x ∘ sigB p))) =
      Fin.init (Fin.init (Fin.init x)) := by
    rw [hvec, Fin.init_snoc]
  simp only [SB, lift2, Set.mem_ofPred_eq, graphOf]
  rw [hfun, hvec, Fin.snoc_last]

/-! ## The projection -/

/-- The projection along the last two coordinates of the combined set is exactly the graph of
the affine combination. -/
theorem proj_comb_eq (p : ℕ) (lo hi : (Fin p → ℝ) → ℝ) (c₁ c₂ c₃ : ℝ) :
    Work.WilG5.projN (n := p+1) 2
      ({x : Fin (p+3) → ℝ | x (uIdx p) = lo (Fin.init (Fin.init (Fin.init x)))} ∩
       {x : Fin (p+3) → ℝ | x (vIdx p) = hi (Fin.init (Fin.init (Fin.init x)))} ∩
       {z : Fin (p+3) → ℝ | z (yIdx p) = c₁ + c₂ * z (uIdx p) + c₃ * z (vIdx p)})
      = graphOf (fun l : Fin p → ℝ => c₁ + c₂ * lo l + c₃ * hi l) := by
  ext x
  simp only [Work.WilG5.projN, graphOf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    rw [append_uIdx, init3_append] at h1
    rw [append_vIdx, init3_append] at h2
    rw [append_yIdx, append_uIdx, append_vIdx] at h3
    rw [h3, h1, h2]
  · intro hx
    refine ⟨![lo (Fin.init x), hi (Fin.init x)], ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [append_uIdx, init3_append]
      simp
    · rw [append_vIdx, init3_append]
      simp
    · rw [append_yIdx, append_uIdx, append_vIdx, hx]
      simp

end Work.WilG4a

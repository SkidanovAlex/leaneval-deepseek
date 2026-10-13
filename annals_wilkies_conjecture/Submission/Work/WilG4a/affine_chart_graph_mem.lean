/-
  WilG4a : the affine-chart lemma of the `n = 1` base case (BNZ §5.1).

  If the graphs of `α` and `β` are `Ω`-definable with format `F` and degree `D`, then so is
  the graph of the one-parameter family `(l, t) ↦ α l + β l * t`, with a format depending
  only on `F` and `p` and a degree bounded by a polynomial in `D` (here: `2 * D + 6`).

  Construction.  Work in `ℝ^{p+4}`, coordinates indexed by `Fin (p+4)`:

    * `0, …, p-1` — the `p` parameters, read by `Fin.castAdd 4`;
    * `acgT p = p`   — the variable `t`;
    * `acgY p = p+1` — the output value `y`;
    * `acgU p = p+2` — a copy of `α` of the parameters;
    * `acgV p = p+3` — a copy of `β` of the parameters.

  The three sets

    * `acgSetA p α = {z | z ∘ iotaA p ∈ graphOf α}`  (so `z (acgU p) = α (params)`),
    * `acgSetB p β = {z | z ∘ iotaB p ∈ graphOf β}`  (so `z (acgV p) = β (params)`),
    * `acgRelSet p  = {z | z (acgY p) = z (acgU p) + z (acgV p) * z (acgT p)}`

  are `Ω`-definable (two substitution atoms `subst_mem_aux` and one degree-`2` hypersurface),
  and the projection of their intersection along the last two coordinates is exactly the
  graph of the family `(l, t) ↦ α l + β l * t`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG0.liftNM_mem
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.projLastIter_eq

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-! ## The ambient coordinates of `ℝ^{p+4}` -/

/-- The output coordinate `⟨p+1⟩` of `Fin (p+4)` (the value `y`). -/
def acgY (p : ℕ) : Fin (p+4) := ⟨p+1, by omega⟩

/-- The coordinate `⟨p+2⟩` of `Fin (p+4)`: where `α` of the parameters is recorded. -/
def acgU (p : ℕ) : Fin (p+4) := ⟨p+2, by omega⟩

/-- The coordinate `⟨p+3⟩` of `Fin (p+4)`: where `β` of the parameters is recorded. -/
def acgV (p : ℕ) : Fin (p+4) := ⟨p+3, by omega⟩

/-- The coordinate `⟨p⟩` of `Fin (p+4)`: the variable `t`. -/
def acgT (p : ℕ) : Fin (p+4) := ⟨p, by omega⟩

/-- `Fin (p+1) → Fin (p+4)` reading `(parameters, u)`: the first `p` coordinates are kept,
the last one is sent to `acgU p`. -/
def acgIotaA (p : ℕ) : Fin (p+1) → Fin (p+4) :=
  Fin.lastCases (acgU p) (fun i => Fin.castAdd 4 i)

/-- `Fin (p+1) → Fin (p+4)` reading `(parameters, v)`: the last coordinate is sent to
`acgV p`. -/
def acgIotaB (p : ℕ) : Fin (p+1) → Fin (p+4) :=
  Fin.lastCases (acgV p) (fun i => Fin.castAdd 4 i)

@[simp] theorem acgIotaA_last (p : ℕ) : acgIotaA p (Fin.last p) = acgU p := by
  simp [acgIotaA]

@[simp] theorem acgIotaA_castSucc (p : ℕ) (i : Fin p) :
    acgIotaA p (Fin.castSucc i) = Fin.castAdd 4 i := by
  simp [acgIotaA]

@[simp] theorem acgIotaB_last (p : ℕ) : acgIotaB p (Fin.last p) = acgV p := by
  simp [acgIotaB]

@[simp] theorem acgIotaB_castSucc (p : ℕ) (i : Fin p) :
    acgIotaB p (Fin.castSucc i) = Fin.castAdd 4 i := by
  simp [acgIotaB]

/-! ## The two graph pieces and the relation set -/

/-- The set "`z (acgU p) = α` of the parameters" inside `ℝ^{p+4}`. -/
def acgSetA (p : ℕ) (α : (Fin p → ℝ) → ℝ) : Set (Fin (p+4) → ℝ) :=
  {z | z ∘ acgIotaA p ∈ WilkiesDesign.graphOf α}

/-- The set "`z (acgV p) = β` of the parameters" inside `ℝ^{p+4}`. -/
def acgSetB (p : ℕ) (β : (Fin p → ℝ) → ℝ) : Set (Fin (p+4) → ℝ) :=
  {z | z ∘ acgIotaB p ∈ WilkiesDesign.graphOf β}

/-- The hypersurface `y = u + v * t`. -/
def acgRelPoly (p : ℕ) : MvPolynomial (Fin (p+4)) ℝ :=
  MvPolynomial.X (acgY p) - MvPolynomial.X (acgU p) -
    MvPolynomial.X (acgV p) * MvPolynomial.X (acgT p)

/-- The relation `z (acgY p) = z (acgU p) + z (acgV p) * z (acgT p)`. -/
def acgRelSet (p : ℕ) : Set (Fin (p+4) → ℝ) :=
  {z | z (acgY p) = z (acgU p) + z (acgV p) * z (acgT p)}

theorem mem_acgSetA {p : ℕ} (α : (Fin p → ℝ) → ℝ) (z : Fin (p+4) → ℝ) :
    z ∈ acgSetA p α ↔ z (acgU p) = α (fun i : Fin p => z (Fin.castAdd 4 i)) := by
  have h1 : (z ∘ acgIotaA p) (Fin.last p) = z (acgU p) := by
    rw [Function.comp_apply, acgIotaA_last]
  have h2 : Fin.init (z ∘ acgIotaA p) = (fun i : Fin p => z (Fin.castAdd 4 i)) := by
    funext i
    show (z ∘ acgIotaA p) (Fin.castSucc i) = z (Fin.castAdd 4 i)
    rw [Function.comp_apply, acgIotaA_castSucc]
  show (z ∘ acgIotaA p) (Fin.last p) = α (Fin.init (z ∘ acgIotaA p)) ↔
    z (acgU p) = α (fun i : Fin p => z (Fin.castAdd 4 i))
  constructor
  · intro hh; rwa [h1, h2] at hh
  · intro hh; rwa [← h1, ← h2] at hh

theorem mem_acgSetB {p : ℕ} (β : (Fin p → ℝ) → ℝ) (z : Fin (p+4) → ℝ) :
    z ∈ acgSetB p β ↔ z (acgV p) = β (fun i : Fin p => z (Fin.castAdd 4 i)) := by
  have h1 : (z ∘ acgIotaB p) (Fin.last p) = z (acgV p) := by
    rw [Function.comp_apply, acgIotaB_last]
  have h2 : Fin.init (z ∘ acgIotaB p) = (fun i : Fin p => z (Fin.castAdd 4 i)) := by
    funext i
    show (z ∘ acgIotaB p) (Fin.castSucc i) = z (Fin.castAdd 4 i)
    rw [Function.comp_apply, acgIotaB_castSucc]
  show (z ∘ acgIotaB p) (Fin.last p) = β (Fin.init (z ∘ acgIotaB p)) ↔
    z (acgV p) = β (fun i : Fin p => z (Fin.castAdd 4 i))
  constructor
  · intro hh; rwa [h1, h2] at hh
  · intro hh; rwa [← h1, ← h2] at hh

theorem mem_acgRelSet (p : ℕ) (z : Fin (p+4) → ℝ) :
    z ∈ acgRelSet p ↔ z (acgY p) = z (acgU p) + z (acgV p) * z (acgT p) := by
  simp [acgRelSet]

theorem acgRelPoly_set (p : ℕ) :
    {z : Fin (p+4) → ℝ | MvPolynomial.eval z (acgRelPoly p) = 0} = acgRelSet p := by
  ext z
  simp only [Set.mem_ofPred_eq, acgRelSet]
  rw [show MvPolynomial.eval z (acgRelPoly p) =
      z (acgY p) - z (acgU p) - z (acgV p) * z (acgT p) from by simp [acgRelPoly]]
  constructor <;> intro h <;> linarith

theorem acgRelPoly_totalDegree_le (p : ℕ) : (acgRelPoly p).totalDegree ≤ 2 := by
  have ha : (MvPolynomial.X (acgY p) - MvPolynomial.X (acgU p) :
      MvPolynomial (Fin (p+4)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    decide
  have hb : (MvPolynomial.X (acgV p) * MvPolynomial.X (acgT p) :
      MvPolynomial (Fin (p+4)) ℝ).totalDegree ≤ 2 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  have h : (acgRelPoly p).totalDegree ≤ max 1 2 := by
    rw [acgRelPoly]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · exact le_trans ha (le_max_left 1 2)
    · exact le_trans hb (le_max_right 1 2)
  exact le_trans h (by decide)

/-! ## Substitution (a clean version of `subst_mem`, using the *proved* `liftNM_mem`) -/

/-- The pullback `{x | x ∘ ι ∈ A}` of an `Ω F D m`-set `A` along a coordinate map
`ι : Fin m → Fin n` is an `Ω`-set of dimension `n`, format `F + 2 * (n + m) + 1` and
degree `D + 2`.

This is `Work.WilG4a.subst_mem` with the (proved) `Work.WilG0.liftNM_mem` in place of the
placeholder in `Work.WilG4a.liftNM_mem`. -/
theorem subst_mem_aux (S : WilkiesDesign.SOMin) {m n : ℕ} (ι : Fin m → Fin n) {F D : ℕ}
    {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) :
    {x : Fin n → ℝ | x ∘ ι ∈ A} ∈ S.Ω (F + 2 * (n + m) + 1) (D + 2) n := by
  have hlift : Work.WilG0.liftNM n m A ∈ S.Ω (F + n) D (n + m) :=
    Work.WilG0.liftNM_mem hA n
  have hdiag : Work.WilG0.diagSet n m ι ∈ S.Ω (n + m) 2 (n + m) := diagSet_mem S n m ι
  have h1 : Work.WilG0.liftNM n m A ∈ S.Ω (max (F + n) (n + m)) D (n + m) :=
    mem_mono hlift (le_max_left _ _) le_rfl
  have h2 : Work.WilG0.diagSet n m ι ∈ S.Ω (max (F + n) (n + m)) 2 (n + m) :=
    mem_mono hdiag (le_max_right _ _) le_rfl
  have h3 : (Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι) ∈
      S.Ω (max (F + n) (n + m) + 1) (D + 2) (n + m) := by
    have h := S.inter (fun i : Fin 2 => if i = 0 then D else 2)
      (fun i : Fin 2 => if i = 0 then Work.WilG0.liftNM n m A else Work.WilG0.diagSet n m ι)
      (by intro i; fin_cases i
          · simpa using h1
          · simpa using h2)
    have hsum : (∑ i : Fin 2, (if i = 0 then D else 2)) = D + 2 := by
      rw [Fin.sum_univ_two]; norm_num
    rw [hsum] at h
    rwa [iInter_fin_two] at h
  have h4 : Work.WilG0.projLastIter n m
      (Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι) ∈
      S.Ω (max (F + n) (n + m) + 1 + m) (D + 2) n :=
    projLastIter_mem (S := S) (n := n) (m := m) h3
  have h5 : Work.WilG0.projLastIter n m
      (Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι) ∈
      S.Ω (F + 2 * (n + m) + 1) (D + 2) n := mem_mono h4 (by omega) le_rfl
  rw [subst_lift_eq]
  exact h5

/-! ## Binary intersection of `Ω`-sets at a common format -/

theorem iInter_fin_two_ac_y {α : Type*} (A : Fin 2 → Set α) : (⋂ i, A i) = A 0 ∩ A 1 := by
  ext z
  simp [Set.mem_iInter, Fin.forall_fin_two]

/-- `SOMin.inter` in the binary case. -/
theorem inter_mem2 {S : WilkiesDesign.SOMin} {n : ℕ} {F D1 D2 : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D1 n) (hB : B ∈ S.Ω F D2 n) : A ∩ B ∈ S.Ω (F + 1) (D1 + D2) n := by
  have h : ∀ i : Fin 2, (![A, B] i) ∈ S.Ω F (![D1, D2] i) n := by
    intro i; fin_cases i
    · simpa using hA
    · simpa using hB
  have hmain := S.inter ![D1, D2] ![A, B] h
  rw [iInter_fin_two_ac_y] at hmain
  have hsum : (∑ i : Fin 2, ![D1, D2] i) = D1 + D2 := by simp [Fin.sum_univ_two]
  rw [hsum] at hmain
  exact hmain

theorem acgRelSet_mem (S : WilkiesDesign.SOMin) (p : ℕ) :
    acgRelSet p ∈ S.Ω (p+4) 2 (p+4) := by
  have h := S.hyp (p+4) (acgRelPoly p)
  rw [acgRelPoly_set] at h
  exact mem_mono h le_rfl (acgRelPoly_totalDegree_le p)

/-! ## Index arithmetic for the projection -/

theorem acgSnocU (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 2 → ℝ) :
    Work.WilG0.snocIt (p+2) 2 x w (acgU p) = w 0 := by
  rw [show (acgU p : Fin (p+4)) = Fin.natAdd (p+2) (0 : Fin 2) from Fin.ext rfl]
  exact Work.WilG0.snocIt_natAdd (p+2) 2 x w 0

theorem acgSnocV (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 2 → ℝ) :
    Work.WilG0.snocIt (p+2) 2 x w (acgV p) = w 1 := by
  rw [show (acgV p : Fin (p+4)) = Fin.natAdd (p+2) (1 : Fin 2) from Fin.ext rfl]
  exact Work.WilG0.snocIt_natAdd (p+2) 2 x w 1

theorem acgSnocY (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 2 → ℝ) :
    Work.WilG0.snocIt (p+2) 2 x w (acgY p) = x (Fin.last (p+1)) := by
  rw [show (acgY p : Fin (p+4)) = Fin.castAdd 2 (Fin.last (p+1)) from Fin.ext rfl]
  exact Work.WilG0.snocIt_castAdd (p+2) 2 x w (Fin.last (p+1))

theorem acgSnocT (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 2 → ℝ) :
    Work.WilG0.snocIt (p+2) 2 x w (acgT p) = x (Fin.castSucc (Fin.last p)) := by
  rw [show (acgT p : Fin (p+4)) = Fin.castAdd 2 (Fin.castSucc (Fin.last p)) from Fin.ext rfl]
  exact Work.WilG0.snocIt_castAdd (p+2) 2 x w (Fin.castSucc (Fin.last p))

theorem acgSnocPar (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 2 → ℝ) (i : Fin p) :
    Work.WilG0.snocIt (p+2) 2 x w (Fin.castAdd 4 i) = x (Fin.castAdd 2 i) := by
  rw [show (Fin.castAdd 4 i : Fin (p+4)) = Fin.castAdd 2 (Fin.castAdd 2 i) from Fin.ext rfl]
  exact Work.WilG0.snocIt_castAdd (p+2) 2 x w (Fin.castAdd 2 i)

theorem acgSnocParFun (p : ℕ) (x : Fin (p+2) → ℝ) (w : Fin 2 → ℝ) :
    (fun i : Fin p => Work.WilG0.snocIt (p+2) 2 x w (Fin.castAdd 4 i)) =
      (fun i : Fin p => x (Fin.castAdd 2 i)) :=
  funext (fun i => acgSnocPar p x w i)

theorem acgParFun (p : ℕ) (x : Fin (p+2) → ℝ) :
    (fun i : Fin p => x (Fin.castAdd 2 i)) =
      (fun i : Fin p => x (Fin.castSucc (Fin.castSucc i))) := by
  funext i
  rw [show (Fin.castSucc (Fin.castSucc i) : Fin (p+2)) = Fin.castAdd 2 i from Fin.ext rfl]

/-! ## The set identity -/

theorem acgProj_eq (p : ℕ) (α β : (Fin p → ℝ) → ℝ) :
    Work.WilG0.projLastIter (p+2) 2 (acgSetA p α ∩ acgSetB p β ∩ acgRelSet p) =
      graphFam (fun l (t : ℝ) => α l + β l * t) := by
  rw [Work.WilG0.projLastIter_eq]
  ext x
  rw [mem_graphFam]
  show (∃ w : Fin 2 → ℝ,
      Work.WilG0.snocIt (p+2) 2 x w ∈ acgSetA p α ∩ acgSetB p β ∩ acgRelSet p) ↔
    x (Fin.last (p+1)) = α (fun i : Fin p => x (Fin.castSucc (Fin.castSucc i))) +
      β (fun i : Fin p => x (Fin.castSucc (Fin.castSucc i))) * x (Fin.castSucc (Fin.last p))
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff, Set.mem_inter_iff] at hw
    obtain ⟨⟨hA, hB⟩, hR⟩ := hw
    rw [mem_acgSetA] at hA
    rw [acgSnocU, acgSnocParFun] at hA
    rw [mem_acgSetB] at hB
    rw [acgSnocV, acgSnocParFun] at hB
    rw [mem_acgRelSet] at hR
    rw [acgSnocY, acgSnocU, acgSnocV, acgSnocT] at hR
    rw [acgParFun] at hA hB
    rw [← hA, ← hB]
    exact hR
  · intro hx
    rw [← acgParFun] at hx
    set w : Fin 2 → ℝ := ![
      α (fun i : Fin p => x (Fin.castAdd 2 i)),
      β (fun i : Fin p => x (Fin.castAdd 2 i))] with hwdef
    have hw0 : w 0 = α (fun i : Fin p => x (Fin.castAdd 2 i)) := by simp [hwdef]
    have hw1 : w 1 = β (fun i : Fin p => x (Fin.castAdd 2 i)) := by simp [hwdef]
    refine ⟨w, ?_⟩
    rw [Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_acgSetA, acgSnocU, acgSnocParFun]
      exact hw0
    · rw [mem_acgSetB, acgSnocV, acgSnocParFun]
      exact hw1
    · rw [mem_acgRelSet, acgSnocY, acgSnocU, acgSnocV, acgSnocT, hw0, hw1]
      exact hx

/-! ## The format and degree bookkeeping -/

/-- The format produced by two substitution atoms at `F`, an intersection and a projection. -/
def acgBase (p F : ℕ) : ℕ := max (F + 2 * ((p+4) + (p+1)) + 1) (p+4)

/-- The degree polynomial: it evaluates to `2 * D + 6`. -/
def acgBPoly : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.C 6 + MvPolynomial.C 2 * MvPolynomial.X 0

theorem acgBPoly_eval (D r : ℕ) : MvPolynomial.eval ![D, r] acgBPoly = 2 * D + 6 := by
  have h : MvPolynomial.eval ![D, r] acgBPoly = 6 + 2 * D := by simp [acgBPoly]
  rw [h]; ring

theorem affine_chart_graph_mem (S : WilkiesDesign.SOMin) (p : ℕ) (F : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {α β : (Fin p → ℝ) → ℝ}, WilkiesDesign.graphOf α ∈ S.Ω F D (p + 1) → WilkiesDesign.graphOf β ∈ S.Ω F D (p + 1) → Work.WilG4a.graphFam (fun l (t : ℝ) => α l + β l * t) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1) := by
  refine ⟨acgBase p F + 4, acgBPoly, ?_⟩
  intro D r α β hα hβ
  have hA : acgSetA p α ∈ S.Ω (F + 2 * ((p+4) + (p+1)) + 1) (D + 2) (p+4) :=
    subst_mem_aux S (acgIotaA p) hα
  have hB : acgSetB p β ∈ S.Ω (F + 2 * ((p+4) + (p+1)) + 1) (D + 2) (p+4) :=
    subst_mem_aux S (acgIotaB p) hβ
  have hR : acgRelSet p ∈ S.Ω (p+4) 2 (p+4) := acgRelSet_mem S p
  have hA' : acgSetA p α ∈ S.Ω (acgBase p F) (D + 2) (p+4) :=
    mem_mono hA (le_max_left _ _) le_rfl
  have hB' : acgSetB p β ∈ S.Ω (acgBase p F) (D + 2) (p+4) :=
    mem_mono hB (le_max_left _ _) le_rfl
  have hR' : acgRelSet p ∈ S.Ω (acgBase p F) 2 (p+4) :=
    mem_mono hR (le_max_right _ _) le_rfl
  have hR'' : acgRelSet p ∈ S.Ω (acgBase p F + 1) 2 (p+4) :=
    mem_mono hR' (by omega) le_rfl
  have hI : (acgSetA p α ∩ acgSetB p β ∩ acgRelSet p) ∈
      S.Ω (acgBase p F + 1 + 1) ((D+2) + (D+2) + 2) (p+4) :=
    inter_mem2 (inter_mem2 hA' hB') hR''
  have hP : Work.WilG0.projLastIter (p+2) 2 (acgSetA p α ∩ acgSetB p β ∩ acgRelSet p) ∈
      S.Ω (acgBase p F + 1 + 1 + 2) ((D+2) + (D+2) + 2) (p+2) :=
    projLastIter_mem (S := S) (n := p+2) (m := 2) hI
  rw [acgProj_eq p α β] at hP
  rw [acgBPoly_eval]
  exact mem_mono hP (by omega) (by omega)

end Work.WilG4a

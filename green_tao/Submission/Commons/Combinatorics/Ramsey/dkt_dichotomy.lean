import Mathlib
import Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj
import Submission.Commons.Combinatorics.Ramsey.kvec_injective
import Submission.Commons.Combinatorics.Ramsey.card_varWord
import Submission.Commons.Combinatorics.Ramsey.dkt_exists_goodline

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

/-! ## Infrastructure: composition and lifting of combinatorial subspaces -/

/-- The index word of the line inside `S` obtained by substituting `σ`. -/
def substIdx (M m k : ℕ) (S : Subspace (Fin m) (Fin k) (Fin M))
    (σ : Fin m → Option (Fin k)) : Fin M → Option (Fin k) :=
  fun i => (S.idxFun i).elim (fun a => some a) σ

lemma substIdx_eq (M m k : ℕ) (S : Subspace (Fin m) (Fin k) (Fin M))
    (σ : Fin m → Option (Fin k)) :
    substIdx M m k S σ = fun i => Sum.elim (fun a => some a) σ (S.idxFun i) := by
  funext i
  rcases h : S.idxFun i with a | e <;> simp [substIdx, h]

/-- Lift a subspace of `[k]^M` to a subspace of `[k+1]^M` (cast every letter). -/
def liftSub (M m k : ℕ) (S : Subspace (Fin m) (Fin k) (Fin M)) :
    Subspace (Fin m) (Fin (k+1)) (Fin M) where
  idxFun i := (S.idxFun i).map Fin.castSucc id
  proper e := by
    obtain ⟨i, hi⟩ := S.proper e
    exact ⟨i, by simp [hi]⟩

/-- Composition: run `S` first, then `V`. -/
def compSub {M m k l : ℕ} (V : Subspace (Fin M) (Fin (k+1)) (Fin l))
    (S : Subspace (Fin m) (Fin (k+1)) (Fin M)) : Subspace (Fin m) (Fin (k+1)) (Fin l) where
  idxFun i := (V.idxFun i).elim (fun a => Sum.inl a) S.idxFun
  proper e := by
    obtain ⟨i, hi⟩ := S.proper e
    obtain ⟨j, hj⟩ := V.proper i
    exact ⟨j, by rw [hj]; exact hi⟩

lemma compSub_apply {M m k l : ℕ} (V : Subspace (Fin M) (Fin (k+1)) (Fin l))
    (S : Subspace (Fin m) (Fin (k+1)) (Fin M)) (x : Fin m → Fin (k+1)) :
    compSub V S x = V (S x) := by
  funext i
  rw [Subspace.apply_def, Subspace.apply_def]
  rcases h : V.idxFun i with a | i'
  · dsimp only [compSub]; rw [h]; rfl
  · dsimp only [compSub]; rw [h]; rfl

lemma liftSub_linePt (M m k : ℕ) (S : Subspace (Fin m) (Fin k) (Fin M))
    (g : Fin m → Option (Fin k)) (v : Fin k) :
    liftSub M m k S (linePt g v) = linePt (substIdx M m k S g) v := by
  funext i
  rw [Subspace.apply_def]
  dsimp only [liftSub]
  rcases h : S.idxFun i with a | e <;> simp [substIdx, h, linePt]

/-- Extend a subspace of `[k+1]^l` to a subspace of `[k+1]^n` by a constant suffix `y`. -/
def extendSub (m k l n : ℕ) (U : Subspace (Fin m) (Fin (k+1)) (Fin l)) (h : l ≤ n)
    (y : Fin (n-l) → Fin (k+1)) : Subspace (Fin m) (Fin (k+1)) (Fin n) where
  idxFun i := if hi : (i : ℕ) < l then U.idxFun ⟨i, hi⟩
    else Sum.inl (y ⟨(i:ℕ) - l, by omega⟩)
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    refine ⟨⟨(i:ℕ), by omega⟩, ?_⟩
    have hlt : ((⟨(i:ℕ), by omega⟩ : Fin n) : ℕ) < l := i.isLt
    rw [dif_pos hlt]
    simpa using hi

lemma extendSub_idx_of_lt {m k l n : ℕ} (U : Subspace (Fin m) (Fin (k+1)) (Fin l)) (h : l ≤ n)
    (y : Fin (n-l) → Fin (k+1)) (i : Fin n) (hi : (i:ℕ) < l) :
    (extendSub m k l n U h y).idxFun i = U.idxFun ⟨i, hi⟩ := by
  dsimp only [extendSub]
  rw [dif_pos hi]

lemma extendSub_idx_of_ge {m k l n : ℕ} (U : Subspace (Fin m) (Fin (k+1)) (Fin l)) (h : l ≤ n)
    (y : Fin (n-l) → Fin (k+1)) (i : Fin n) (hi : ¬ (i:ℕ) < l) :
    (extendSub m k l n U h y).idxFun i = Sum.inl (y ⟨(i:ℕ) - l, by omega⟩) := by
  dsimp only [extendSub]
  rw [dif_neg hi]

lemma extendSub_apply (m k l n : ℕ) (U : Subspace (Fin m) (Fin (k+1)) (Fin l)) (h : l ≤ n)
    (y : Fin (n-l) → Fin (k+1)) (x : Fin m → Fin (k+1)) :
    extendSub m k l n U h y x = cat h (U x) y := by
  funext i
  rw [Subspace.apply_def]
  by_cases hi : (i:ℕ) < l
  · rw [extendSub_idx_of_lt U h y i hi,
      cat_apply_of_lt h (U x) y i hi, Subspace.apply_def]
  · rw [extendSub_idx_of_ge U h y i hi, cat_apply_of_ge h (U x) y i hi]
    refine congrArg y (Fin.ext ?_)
    simp

/-! ## Auxiliary counting lemmas -/

/-- Double counting: `∑_y #{x : P x y} = ∑_x #{y : P x y}`. -/
lemma sum_card_filter_comm_nat {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [DecidableRel P] :
    (∑ y : β, (Finset.univ.filter (fun x : α => P x y)).card)
      = ∑ x : α, (Finset.univ.filter (fun y : β => P x y)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

lemma sum_card_filter_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [DecidableRel P] :
    (∑ y : β, ((Finset.univ.filter (fun x : α => P x y)).card : ℝ))
      = ∑ x : α, ((Finset.univ.filter (fun y : β => P x y)).card : ℝ) := by
  exact_mod_cast sum_card_filter_comm_nat P

/-- Level-set lower bound: if `f` takes values in `[0,c]` on a finite type `ι` and has average at
least `ρ`, then the set where `f ≥ d` occupies at least a `(ρ-d)/(c-d)`-fraction of `ι`. -/
lemma level_card_lower {ι : Type*} [Fintype ι] (f : ι → ℝ) (c d ρ : ℝ)
    (hf1 : ∀ i, f i ≤ c)
    (hsum : ρ * (Fintype.card ι : ℝ) ≤ ∑ i, f i) (hdc : d < c) :
    (ρ - d) / (c - d) * (Fintype.card ι : ℝ)
      ≤ ((Finset.univ.filter (fun i => d ≤ f i)).card : ℝ) := by
  classical
  have hcd : 0 < c - d := sub_pos.mpr hdc
  set B : Finset ι := Finset.univ.filter (fun i => d ≤ f i) with hB
  have hsplit : ∑ i, f i = ∑ i ∈ B, f i + ∑ i ∈ Bᶜ, f i :=
    (Finset.sum_add_sum_compl B f).symm
  have h1 : ∑ i ∈ B, f i ≤ (B.card : ℝ) * c := by
    calc ∑ i ∈ B, f i ≤ ∑ _i ∈ B, c := Finset.sum_le_sum (fun i _ => hf1 i)
      _ = (B.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Bᶜ, f i ≤ (Bᶜ.card : ℝ) * d := by
    calc ∑ i ∈ Bᶜ, f i ≤ ∑ _i ∈ Bᶜ, d := Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_compl, hB, Finset.mem_filter] at hi
          exact le_of_lt (not_le.mp (fun h => hi ⟨Finset.mem_univ i, h⟩)))
      _ = (Bᶜ.card : ℝ) * d := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_compl : (Bᶜ.card : ℝ) = (Fintype.card ι : ℝ) - (B.card : ℝ) := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ B)]
  have hmain : (ρ - d) * (Fintype.card ι : ℝ) ≤ (B.card : ℝ) * (c - d) := by
    have := hsum
    rw [hsplit] at this
    have h3 := add_le_add h1 h2
    rw [hcard_compl] at h3
    nlinarith [this, h3]
  rw [div_mul_eq_mul_div, div_le_iff₀ hcd]
  exact hmain

/-- Restricted double counting. -/
lemma sum_card_filter_comm_left_nat {α β : Type*} [Fintype β] [DecidableEq α]
    (s : Finset α) (P : α → β → Prop) [DecidableRel P] :
    (∑ a ∈ s, (Finset.univ.filter (fun b => P a b)).card)
      = ∑ b : β, (s.filter (fun a => P a b)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

lemma sum_card_filter_comm_left {α β : Type*} [Fintype β] [DecidableEq α]
    (s : Finset α) (P : α → β → Prop) [DecidableRel P] :
    (∑ a ∈ s, ((Finset.univ.filter (fun b => P a b)).card : ℝ))
      = ∑ b : β, ((s.filter (fun a => P a b)).card : ℝ) := by
  exact_mod_cast sum_card_filter_comm_left_nat s P

/-- From a subspace `U` of `[k+1]^l` that is slice-dense and line-dense, produce the subspace
`W` of `[k+1]^n` in the second alternative of the dichotomy. -/
theorem dkt_w_from_u (k m l n : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hl : l < n)
    (δ θ η : ℝ) (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hη0 : 0 < η) (hηθ : η < θ / 2)
    (A : Finset (Fin n → Fin (k+1)))
    (U : Subspace (Fin m) (Fin (k+1)) (Fin l))
    (ha : ∀ x : Fin m → Fin (k+1),
      (δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
        (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => cat (le_of_lt hl) (U x) y ∈ A)).card : ℝ))
    (hb : ∀ g ∈ varWord k m,
      θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
        (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y ∈ A)).card : ℝ))
    (hX : ∀ X : Subspace (Fin m) (Fin (k+1)) (Fin n),
      (((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => X x ∈ A)).card : ℝ)
        < (δ + η^2/2) * (((k+1 : ℕ) : ℝ) ^ m)) :
    ∃ W : Subspace (Fin m) (Fin (k+1)) (Fin n),
      (δ - 2*η) * (((k+1 : ℕ) : ℝ) ^ m) ≤
        (((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => W x ∈ A)).card : ℝ) ∧
      (θ/2) * ((((k+1 : ℕ) : ℝ) ^ m) - ((k : ℝ) ^ m)) ≤
        (((varWord k m).filter
          (fun g => ∀ v : Fin k, W (linePt g v) ∈ A)).card : ℝ) := by
  classical
  set q : ℝ := ((k+1 : ℕ) : ℝ) with hq
  have hq2 : (2:ℝ) ≤ q := by rw [hq]; push_cast; exact_mod_cast (by omega : 2 ≤ k+1)
  have hqpos : 0 < q := by linarith
  set Pn : ℕ := (k+1)^(n-l) with hPn
  set Pm : ℕ := (k+1)^m with hPm
  set Vw : ℕ := (varWord k m).card with hVw
  have hPnpos : 0 < Pn := pow_pos (by omega) _
  have hPmpos : 0 < Pm := pow_pos (by omega) _
  have hVwpos : 0 < Vw := by
    rw [hVw]
    exact Finset.card_pos.mpr ⟨(fun _ : Fin m => (none : Option (Fin k))),
      mem_varWord.mpr ⟨⟨0, by omega⟩, rfl⟩⟩
  have hPnq : (Pn : ℝ) = q^(n-l) := by rw [hPn, hq]; push_cast; ring
  have hPmq : (Pm : ℝ) = q^m := by rw [hPm, hq]; push_cast; ring
  have hVwq : (Vw : ℝ) = q^m - (k:ℝ)^m := by
    rw [hVw, card_varWord, hq]
    have hle : k^m ≤ (k+1)^m := Nat.pow_le_pow_left (by omega) m
    rw [Nat.cast_sub hle]; push_cast; ring
  let cnt : (Fin (n-l) → Fin (k+1)) → ℝ := fun y =>
    ((Finset.univ.filter (fun x : Fin m → Fin (k+1) => cat (le_of_lt hl) (U x) y ∈ A)).card : ℝ)
  let lcnt : (Fin (n-l) → Fin (k+1)) → ℝ := fun y =>
    (((varWord k m).filter (fun g => ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y ∈ A)).card : ℝ)
  have hcnt_le : ∀ y, cnt y ≤ (Pm : ℝ) := by
    intro y
    have h1 : (Finset.univ.filter (fun x : Fin m → Fin (k+1) => cat (le_of_lt hl) (U x) y ∈ A)).card ≤ Pm := by
      have := Finset.card_le_univ (Finset.univ.filter (fun x : Fin m → Fin (k+1) => cat (le_of_lt hl) (U x) y ∈ A))
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
      exact this
    simp only [cnt]
    exact_mod_cast h1
  have hlcnt_le : ∀ y, lcnt y ≤ (Vw : ℝ) := by
    intro y
    have h1 : ((varWord k m).filter (fun g => ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y ∈ A)).card ≤ Vw := by
      rw [hVw]; exact Finset.card_le_card (Finset.filter_subset _ _)
    simp only [lcnt]
    exact_mod_cast h1
  have hcard_amb : (Fintype.card (Fin (n-l) → Fin (k+1)) : ℝ) = (Pn : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hPn]
  have hcardm : (Fintype.card (Fin m → Fin (k+1)) : ℝ) = (Pm : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hPm]
  -- lower bound on the average of `cnt`
  have hx : ∀ x : Fin m → Fin (k+1), (δ - η^2/2) * q^(n-l) ≤
      ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) => cat (le_of_lt hl) (U x) y ∈ A)).card : ℝ) :=
    fun x => ha x
  have hxsum : (δ - η^2/2) * (Pm:ℝ) * (Pn:ℝ) ≤ ∑ y, cnt y := by
    have h1 : (δ - η^2/2) * q^m * q^(n-l) ≤ ∑ y, cnt y := by
      calc (δ - η^2/2) * q^m * q^(n-l)
          = (Pm : ℝ) * ((δ - η^2/2) * q^(n-l)) := by rw [hPmq]; ring
        _ = ∑ _x : Fin m → Fin (k+1), (δ - η^2/2) * q^(n-l) := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcardm]
        _ ≤ ∑ x : Fin m → Fin (k+1),
              ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) => cat (le_of_lt hl) (U x) y ∈ A)).card : ℝ) :=
              Finset.sum_le_sum (fun x _ => hx x)
        _ = ∑ y, cnt y := by
              simp only [cnt]
              exact (sum_card_filter_comm (fun x y => cat (le_of_lt hl) (U x) y ∈ A)).symm
    rw [hPmq, hPnq]
    exact h1
  -- lower bound on the average of `lcnt`
  have hg : ∀ g ∈ varWord k m, θ * q^(n-l) ≤
      ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
        ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y ∈ A)).card : ℝ) :=
    fun g hg => hb g hg
  have hlsum : θ * (Vw:ℝ) * (Pn:ℝ) ≤ ∑ y, lcnt y := by
    have h1 : θ * (Vw:ℝ) * q^(n-l) ≤ ∑ y, lcnt y := by
      calc θ * (Vw:ℝ) * q^(n-l)
          = ∑ g ∈ varWord k m, θ * q^(n-l) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ g ∈ varWord k m,
              ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
                ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y ∈ A)).card : ℝ) :=
              Finset.sum_le_sum hg
        _ = ∑ y, lcnt y := by
              simp only [lcnt]
              exact (sum_card_filter_comm_left (varWord k m)
                (fun g y => ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y ∈ A))
    rw [hPnq]
    exact h1
  -- the two level sets
  let H1 : Finset (Fin (n-l) → Fin (k+1)) := Finset.univ.filter (fun y => (δ - 2*η) * (Pm:ℝ) ≤ cnt y)
  let H2 : Finset (Fin (n-l) → Fin (k+1)) := Finset.univ.filter (fun y => (θ/2) * (Vw:ℝ) ≤ lcnt y)
  have hH1 : (1 - η) * (Pn:ℝ) ≤ (H1.card : ℝ) := by
    have hf1 : ∀ y, cnt y ≤ (δ + η^2/2) * (Pm:ℝ) := by
      intro y
      have h := hX (extendSub m k l n U (le_of_lt hl) y)
      have hfilter : (Finset.univ.filter (fun x : Fin m → Fin (k+1) => extendSub m k l n U (le_of_lt hl) y x ∈ A))
          = (Finset.univ.filter (fun x : Fin m → Fin (k+1) => cat (le_of_lt hl) (U x) y ∈ A)) := by
        apply Finset.filter_congr
        intro x _
        rw [extendSub_apply]
      rw [hfilter] at h
      simp only [cnt]
      rw [hPmq]
      exact le_of_lt h
    have hdc : (δ - 2*η) * (Pm:ℝ) < (δ + η^2/2) * (Pm:ℝ) := by
      have hlt : δ - 2*η < δ + η^2/2 := by nlinarith [hη0, sq_nonneg η]
      exact mul_lt_mul_of_pos_right hlt (by exact_mod_cast hPmpos)
    have hsum : ((δ - η^2/2) * (Pm:ℝ)) * (Fintype.card (Fin (n-l) → Fin (k+1)) : ℝ) ≤ ∑ y, cnt y := by
      rw [hcard_amb]; exact hxsum
    have hlev := level_card_lower cnt ((δ + η^2/2) * (Pm:ℝ)) ((δ - 2*η) * (Pm:ℝ))
      ((δ - η^2/2) * (Pm:ℝ)) hf1 hsum hdc
    have hratio : (2*η - η^2/2)/(2*η + η^2/2)
        = ((δ - η^2/2) * (Pm:ℝ) - (δ - 2*η) * (Pm:ℝ)) / ((δ + η^2/2) * (Pm:ℝ) - (δ - 2*η) * (Pm:ℝ)) := by
      rw [show (δ - η^2/2) * (Pm:ℝ) - (δ - 2*η) * (Pm:ℝ) = (2*η - η^2/2) * (Pm:ℝ) by ring,
          show (δ + η^2/2) * (Pm:ℝ) - (δ - 2*η) * (Pm:ℝ) = (2*η + η^2/2) * (Pm:ℝ) by ring,
          mul_div_mul_right _ _ (by exact_mod_cast (ne_of_gt hPmpos))]
    have hden : 0 < 2*η + η^2/2 := by nlinarith [hη0, sq_nonneg η]
    have hbasic : (1 - η) * (2*η + η^2/2) ≤ 2*η - η^2/2 := by nlinarith [hη0, sq_nonneg η]
    have hstep : (1 - η) * (Pn:ℝ) ≤ ((2*η - η^2/2)/(2*η + η^2/2)) * (Pn:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [le_div_iff₀ hden]
      exact hbasic
    rw [hcard_amb, ← hratio] at hlev
    linarith [hlev, hstep]
  have hH2 : (θ/2) * (Pn:ℝ) ≤ (H2.card : ℝ) := by
    have hdc : (θ/2) * (Vw:ℝ) < (Vw:ℝ) := by
      have hlt : θ/2 < 1 := by linarith
      calc (θ/2) * (Vw:ℝ) < 1 * (Vw:ℝ) := mul_lt_mul_of_pos_right hlt (by exact_mod_cast hVwpos)
        _ = (Vw:ℝ) := one_mul _
    have hsum : (θ * (Vw:ℝ)) * (Fintype.card (Fin (n-l) → Fin (k+1)) : ℝ) ≤ ∑ y, lcnt y := by
      rw [hcard_amb]; exact hlsum
    have hlev := level_card_lower lcnt (Vw:ℝ) ((θ/2) * (Vw:ℝ)) (θ * (Vw:ℝ)) hlcnt_le hsum hdc
    have hratio : (θ/2)/(1 - θ/2) = (θ * (Vw:ℝ) - (θ/2) * (Vw:ℝ)) / ((Vw:ℝ) - (θ/2) * (Vw:ℝ)) := by
      rw [show θ * (Vw:ℝ) - (θ/2) * (Vw:ℝ) = (θ/2) * (Vw:ℝ) by ring,
          show (Vw:ℝ) - (θ/2) * (Vw:ℝ) = (1 - θ/2) * (Vw:ℝ) by ring,
          mul_div_mul_right _ _ (by exact_mod_cast (ne_of_gt hVwpos))]
    have hden : 0 < 1 - θ/2 := by linarith
    have hstep : (θ/2) * (Pn:ℝ) ≤ ((θ/2)/(1 - θ/2)) * (Pn:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [le_div_iff₀ hden]
      nlinarith [hθ]
    rw [hcard_amb, ← hratio] at hlev
    linarith [hlev, hstep]
  -- the two level sets meet
  have hInter : (H1 ∩ H2).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hdisj : Disjoint H1 H2 := Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hu : (H1 ∪ H2).card = H1.card + H2.card := Finset.card_union_of_disjoint hdisj
    have hle : ((H1 ∪ H2).card : ℝ) ≤ (Pn:ℝ) := by
      have h1 : ((H1 ∪ H2).card : ℝ) ≤ (Fintype.card (Fin (n-l) → Fin (k+1)) : ℝ) := by
        exact_mod_cast (Finset.card_le_univ (H1 ∪ H2))
      rwa [hcard_amb] at h1
    have hgt : (Pn:ℝ) < (H1.card : ℝ) + (H2.card : ℝ) := by
      have h1 := hH1; have h2 := hH2
      have hgt1 : (1:ℝ) < (1 - η) + θ/2 := by linarith
      have hPnR : (0:ℝ) < (Pn:ℝ) := by exact_mod_cast hPnpos
      nlinarith [h1, h2, hPnR, mul_pos hPnR (sub_pos.mpr hgt1)]
    have := hle
    rw [hu] at this
    push_cast at this
    linarith
  obtain ⟨y0, hy0⟩ := hInter
  rw [Finset.mem_inter] at hy0
  obtain ⟨hy01, hy02⟩ := hy0
  refine ⟨extendSub m k l n U (le_of_lt hl) y0, ?_, ?_⟩
  · have h1 : (δ - 2*η) * (Pm:ℝ) ≤ cnt y0 := by
      simpa only [H1, Finset.mem_filter, Finset.mem_univ, true_and] using hy01
    have hfilter : (Finset.univ.filter (fun x : Fin m → Fin (k+1) =>
          extendSub m k l n U (le_of_lt hl) y0 x ∈ A))
        = (Finset.univ.filter (fun x : Fin m → Fin (k+1) => cat (le_of_lt hl) (U x) y0 ∈ A)) := by
      apply Finset.filter_congr
      intro x _
      simp only [extendSub_apply]
    rw [hfilter]
    change (δ - 2*η) * q^m ≤ cnt y0
    rw [← hPmq]
    exact h1
  · have h2 : (θ/2) * (Vw:ℝ) ≤ lcnt y0 := by
      simpa only [H2, Finset.mem_filter, Finset.mem_univ, true_and] using hy02
    have hfilter : ((varWord k m).filter (fun g =>
          ∀ v : Fin k, extendSub m k l n U (le_of_lt hl) y0 (linePt g v) ∈ A))
        = ((varWord k m).filter (fun g =>
          ∀ v : Fin k, cat (le_of_lt hl) (U (linePt g v)) y0 ∈ A)) := by
      apply Finset.filter_congr
      intro g _
      simp only [extendSub_apply]
    rw [hfilter]
    change (θ/2) * (q^m - (k:ℝ)^m) ≤ lcnt y0
    rw [← hVwq]
    exact h2

/-- The combinatorial line of `[k]^M` lying inside the subspace `S` obtained by substituting the
variable word `σ`. -/
def lineOfSubst (M m k : ℕ) (S : Subspace (Fin m) (Fin k) (Fin M)) (σ : Fin m → Option (Fin k))
    (hσ : ∃ e, σ e = none) : Line (Fin k) (Fin M) :=
  ⟨substIdx M m k S σ, by
    obtain ⟨e, he⟩ := hσ
    obtain ⟨i, hi⟩ := S.proper e
    exact ⟨i, by simpa [substIdx, hi] using he⟩⟩

/-- The predicate that the line with index word `w` is `θ`-dense in the slices of `A` along `V`. -/
def goodLine (k M l n : ℕ) (θ : ℝ) (A : Finset (Fin n → Fin (k+1)))
    (V : Subspace (Fin M) (Fin (k+1)) (Fin l)) (hl : l < n) (w : Fin M → Option (Fin k)) : Prop :=
  θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
    (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
      (fun y => ∀ v : Fin k, cat (le_of_lt hl) (V (linePt w v)) y ∈ A)).card : ℝ)

theorem dkt_dichotomy (k : ℕ) (hk : 2 ≤ k)
    (hgr : ∀ (M : ℕ), ∃ n : ℕ, ∀ n' : ℕ, n ≤ n' → ∀ C : _root_.Combinatorics.Line (Fin k) (Fin n') → Fin 2,
      ∃ S : _root_.Combinatorics.Subspace (Fin M) (Fin k) (Fin n'), ∃ c : Fin 2,
        ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) →
          C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
              obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
              exact ⟨i, by simp [hi, he]⟩⟩ = c)
    (hl4 : ∀ (K m : ℕ), 2 ≤ K → 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Fin K),
        ε * (K : ℝ) ^ n < (A.card : ℝ) →
        ∃ l : ℕ, ∃ h : l < n, ∃ V : _root_.Combinatorics.Subspace (Fin m) (Fin K) (Fin l),
          ∀ x : Fin m → Fin K,
            ((A.card : ℝ) / (K : ℝ) ^ n - ε) * ((K : ℝ) ^ (n - l)) ≤
              (((Finset.univ : Finset (Fin (n - l) → Fin K)).filter
                 (fun y => Commons.Combinatorics.Ramsey.cat (le_of_lt h) (V x) y ∈ A)).card : ℝ))
    (δ θ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hη : η = δ * θ / 48)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hdhj₀ : ∀ n : ℕ, m₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      (δ / 4) * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : _root_.Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T)
    (hθm : θ * (((k+1 : ℕ) : ℝ) ^ m₀ - (k : ℝ) ^ m₀) ≤ δ / 4)
    (m : ℕ) (hm : m₀ ≤ m) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Fin (k+1)),
      δ * (((k+1 : ℕ) : ℝ)) ^ n ≤ (A.card : ℝ) →
      (∃ X : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
          (δ + η^2/2) * (((k+1 : ℕ) : ℝ)) ^ m ≤
            ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => X x ∈ A)).card) ∨
      (∃ W : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
          (δ - 2*η) * (((k+1 : ℕ) : ℝ)) ^ m ≤
            ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => W x ∈ A)).card ∧
          (θ/2) * ((((k+1 : ℕ) : ℝ) ^ m) - ((k : ℝ) ^ m)) ≤
            (((Commons.Combinatorics.Ramsey.varWord k m).filter
              (fun g => ∀ v : Fin k, W (Commons.Combinatorics.Ramsey.linePt g v) ∈ A)).card : ℝ)) := by
  classical
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηθ : η < θ / 2 := by rw [hη]; nlinarith [hδ, hδ1, hθ, hθ1]
  -- choose the ambient dimension `M` for the Ramsey argument and for Lemma 4
  obtain ⟨ngr, hngr⟩ := hgr m
  set M : ℕ := max (max 1 ngr) m with hMdef
  have hMngr : ngr ≤ M := by rw [hMdef]; omega
  have hM1 : 1 ≤ M := by rw [hMdef]; omega
  have hMm : m ≤ M := by rw [hMdef]; omega
  -- the Lemma-4 parameter
  set ε : ℝ := η^2/2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε < 1 := by
    rw [hεdef]
    have : η ≤ 1/48 := by rw [hη]; nlinarith [hδ, hδ1, hθ, hθ1]
    nlinarith [hη0, this]
  have hεδ : ε < δ := by
    rw [hεdef]
    have : η ≤ δ/48 := by rw [hη]; nlinarith [hδ, hδ1, hθ, hθ1]
    nlinarith [hδ, hδ1, hη0, this]
  obtain ⟨n₀, hn₀⟩ := hl4 (k+1) M (by omega) hM1 ε hεpos hε1
  refine ⟨n₀, fun n hn A hA => ?_⟩
  have hqn : (0:ℝ) < (((k+1 : ℕ) : ℝ)) ^ n := by positivity
  have hAε : ε * (((k+1 : ℕ) : ℝ)) ^ n < (A.card : ℝ) := by
    have h1 := mul_lt_mul_of_pos_right hεδ hqn
    linarith [hA, h1]
  obtain ⟨l, hl, V, hV⟩ := hn₀ n hn A hAε
  have hdens : δ ≤ (A.card : ℝ) / (((k+1 : ℕ) : ℝ)) ^ n := by
    rw [le_div_iff₀ hqn]; exact hA
  -- the recursive slice-density hypothesis for `V`
  have hV' : ∀ x : Fin M → Fin (k+1), (δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
      (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => cat (le_of_lt hl) (V x) y ∈ A)).card : ℝ) := by
    intro x
    have h1 := hV x
    have h2 : δ - η^2/2 ≤ (A.card : ℝ) / (((k+1 : ℕ) : ℝ)) ^ n - ε := by
      rw [hεdef]; linarith
    have h3 : (0:ℝ) ≤ (((k+1 : ℕ) : ℝ) ^ (n - l)) := by positivity
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    linarith [h1, h4]
  -- apply the Hales-Jewett dichotomy inside the Ramsey subspace
  let C : Line (Fin k) (Fin M) → Fin 2 :=
    fun L => if goodLine k M l n θ A V hl L.idxFun then 0 else 1
  obtain ⟨S, c, hSc⟩ := hngr M hMngr C
  -- reformulate hSc in terms of `goodLine` and `substIdx`
  have hmono : ∀ σ : Fin m → Option (Fin k), (∃ e, σ e = none) →
      (goodLine k M l n θ A V hl (substIdx M m k S σ) ↔ c = 0) := by
    intro σ hσ
    have h := hSc σ hσ
    change (if goodLine k M l n θ A V hl
        (fun i => Sum.elim (fun a => some a) σ (S.idxFun i)) then (0:Fin 2) else 1) = c at h
    rw [← substIdx_eq M m k S σ] at h
    constructor
    · intro hg; rw [if_pos hg] at h; exact h.symm
    · intro hc; by_contra hg; rw [hc] at h; rw [if_neg hg] at h
      exact Fin.zero_ne_one h.symm
  -- one good line exists (this is Lemma 7 of DKT)
  obtain ⟨σ₀, hσ₀ne, hσ₀good⟩ := dkt_exists_goodline k m m₀ M l n hk hm₀ hm δ θ η
    hδ hδ1 hθ hθ1 hη hdhj₀ hθm S V hl A hV'
  have hc0 : c = 0 := (hmono σ₀ hσ₀ne).mp hσ₀good
  have hgoodall : ∀ σ : Fin m → Option (Fin k), (∃ e, σ e = none) →
      goodLine k M l n θ A V hl (substIdx M m k S σ) :=
    fun σ hσ => (hmono σ hσ).mpr hc0
  -- the composite subspace `U = V ∘ lift S`
  have hUa : ∀ x : Fin m → Fin (k+1), (δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
      (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => cat (le_of_lt hl) (compSub V (liftSub M m k S) x) y ∈ A)).card : ℝ) := by
    intro x
    have h1 := hV' (liftSub M m k S x)
    rw [compSub_apply]
    exact h1
  have hUb : ∀ g ∈ varWord k m, θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
      (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => ∀ v : Fin k,
            cat (le_of_lt hl) (compSub V (liftSub M m k S) (linePt g v)) y ∈ A)).card : ℝ) := by
    intro g hg
    have h1 := hgoodall g (mem_varWord.mp hg)
    have hfe : (Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
          ∀ v : Fin k, cat (le_of_lt hl) (compSub V (liftSub M m k S) (linePt g v)) y ∈ A))
        = (Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
          ∀ v : Fin k, cat (le_of_lt hl) (V (linePt (substIdx M m k S g) v)) y ∈ A)) := by
      apply Finset.filter_congr
      intro y _
      constructor
      · intro hx v
        have := hx v
        rwa [compSub_apply, liftSub_linePt] at this
      · intro hx v
        rw [compSub_apply, liftSub_linePt]
        exact hx v
    rw [hfe]
    exact h1
  -- finish by cases
  by_cases hX : ∃ X : Subspace (Fin m) (Fin (k+1)) (Fin n),
      (δ + η^2/2) * (((k+1 : ℕ) : ℝ) ^ m) ≤
        ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => X x ∈ A)).card
  · exact Or.inl hX
  · refine Or.inr ?_
    push_neg at hX
    exact dkt_w_from_u k m l n hk (by omega) hl δ θ η hδ hθ hθ1 hη0 hηθ A
      (compSub V (liftSub M m k S)) hUa hUb hX

end

end Commons.Combinatorics.Ramsey

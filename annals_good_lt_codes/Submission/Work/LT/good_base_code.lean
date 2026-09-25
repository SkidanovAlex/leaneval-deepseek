import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_prodSum_pairCond
import Submission.Work.LT.gb_agreement_of_prodExp
import Submission.Work.LT.gb_card_weight
import Submission.Work.LT.gb_card_submodule
import Submission.Work.LT.gb_exists_sparse_param
import Submission.Work.LT.gb_exists_weight_param
import Submission.Work.LT.gb_finrank_kerCode
import Submission.Work.LT.gb_matRank_eq_rowRank
import Submission.Work.LT.gb_zero_rectangle
import Submission.Work.LT.gb_extension
import Submission.Work.LT.gb_rank_le
import Submission.Work.LT.gb_zero_rect_of_star
import Submission.Work.LT.gb_basic
import Submission.Work.LT.gb_card_bad_pair
import Submission.Work.LT.gb_card_fail_star_alt

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.LT

open GB

/-! ## The proof of `Work.LT.good_base_code`

The main ingredients are the counting lemmas of Kalachev--Panteleev (existence of a pair of
parity-check matrices whose kernels satisfy property `(*)` and whose product has no sparse
high-rank element), the deterministic product-expansion criterion, and KP Lemma 1 relating
product expansion to agreement testability. -/

/-- Counting lemma (Kalachev--Panteleev Theorem 1, existence step, "kernel of random parity-check
matrix" model). -/
theorem gb_exists_good_pair {D r : ℕ} (α γ β c : ℝ) (hα : 0 < α)
    (hS : ((smallVecs α D).card : ℝ) ≤ (2 : ℝ) ^ (β * D))
    (hW : ((smallMats γ D).card : ℝ) ≤ (2 : ℝ) ^ (c * D ^ 2))
    (hr1 : 8 * β * (D : ℝ) + 4 ≤ (r : ℝ)) (hr2 : 16 ≤ r)
    (hr3 : c * (D : ℝ) ^ 2 + 2 ≤ (r : ℝ) ^ 2 / 4) :
    ∃ H1 H2 : Fin r → Fin D → ZMod 2, HasStar α r (kerCode H1) ∧ HasStar α r (kerCode H2) ∧
      ∀ x, x ∈ smallMats γ D → r ≤ matRank x → ¬ pairCond H1 H2 x := by
  classical
  have hr2' : (2:ℝ) ≤ (r:ℝ)/8 := by
    have : (16:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr2
    linarith
  let HP := (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2)
  let badH : Finset (Fin r → Fin D → ZMod 2) :=
    Finset.univ.filter (fun H => ¬ HasStar α r (kerCode H))
  let goodX : Finset (Fin D × Fin D → ZMod 2) := (smallMats γ D).filter (fun x => r ≤ matRank x)
  let Bad : Finset HP :=
    ((badH ×ˢ (Finset.univ : Finset (Fin r → Fin D → ZMod 2))) ∪
     ((Finset.univ : Finset (Fin r → Fin D → ZMod 2)) ×ˢ badH)) ∪
    (goodX.biUnion (fun x => Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x)))
  -- number of `H` failing property (*)
  have hbadH : (badH.card : ℝ) ≤ (2 : ℝ) ^ ((r : ℝ) * D - (r : ℝ) / 8) := by
    have hS' : (Nat.card {v : Fin D → ZMod 2 // (hammingNorm v : ℝ) ≤ α * D} : ℝ) ≤
        (2 : ℝ) ^ (β * D) := by
      have h1 : (smallVecs α D) = Finset.univ.filter (fun v : Fin D → ZMod 2 =>
          (hammingNorm v : ℝ) ≤ α * D) := rfl
      rw [h1, card_filter_eq_natCard] at hS
      exact hS
    have h := gb_card_fail_star_alt (D := D) (r := r) (α := α) (β := β) hα hr1 hS'
    have h2 : badH.card = Nat.card {H : Fin r → Fin D → ZMod 2 // ¬ HasStar α r (kerCode H)} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h2]
    calc (Nat.card {H : Fin r → Fin D → ZMod 2 // ¬ HasStar α r (kerCode H)} : ℝ)
        ≤ (2:ℝ)^(r*D) * (2:ℝ)^(-(r:ℝ)/8) := h
      _ = (2:ℝ)^((r:ℝ)*D) * (2:ℝ)^(-(r:ℝ)/8) := by
          rw [rpow_two_mul_nat]
      _ = (2:ℝ)^((r:ℝ)*D - (r:ℝ)/8) := by rw [rpow_two_mul]; congr 1; ring
  -- the two `badH`-slices
  have hBad1 : (((badH ×ˢ (Finset.univ : Finset (Fin r → Fin D → ZMod 2))).card : ℕ) : ℝ) ≤
      (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) := by
    rw [Finset.card_product, Nat.cast_mul, card_univ_hmat]
    calc (badH.card : ℝ) * (2:ℝ)^((r:ℝ)*D)
        ≤ (2:ℝ)^((r:ℝ)*D - (r:ℝ)/8) * (2:ℝ)^((r:ℝ)*D) :=
          mul_le_mul_of_nonneg_right hbadH (Real.rpow_nonneg (by norm_num) _)
      _ = (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) := by rw [rpow_two_mul]; congr 1; ring
  have hBad2 : ((((Finset.univ : Finset (Fin r → Fin D → ZMod 2)) ×ˢ badH).card : ℕ) : ℝ) ≤
      (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) := by
    rw [Finset.card_product, Nat.cast_mul, card_univ_hmat]
    calc (2:ℝ)^((r:ℝ)*D) * (badH.card : ℝ)
        ≤ (2:ℝ)^((r:ℝ)*D) * (2:ℝ)^((r:ℝ)*D - (r:ℝ)/8) :=
          mul_le_mul_of_nonneg_left hbadH (Real.rpow_nonneg (by norm_num) _)
      _ = (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) := by rw [rpow_two_mul]; congr 1; ring
  -- the `x`-slices
  have hBad3 :
      ((goodX.biUnion (fun x => Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x))).card : ℝ) ≤
      (2:ℝ)^(c*(D:ℝ)^2) * (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := by
    have hb : ∀ x ∈ goodX,
        ((Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x)).card : ℝ) ≤
          (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := by
      intro x hx
      have hx2 : r ≤ matRank x := (Finset.mem_filter.mp hx).2
      have h := gb_card_bad_pair (D := D) (r := r) x hx2
      have h2 : (Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x)).card =
          Nat.card {p : HP // pairCond p.1 p.2 x} := card_filter_eq_natCard _
      rw [h2]
      calc (Nat.card {p : HP // pairCond p.1 p.2 x} : ℝ)
          ≤ (2:ℝ)^(2*r*D) * (2:ℝ)^(-(r:ℝ)^2/4) := h
        _ = (2:ℝ)^(2*(r:ℝ)*D) * (2:ℝ)^(-(r:ℝ)^2/4) := by
            rw [rpow_two_mul_nat_two]
        _ = (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := by rw [rpow_two_mul]; congr 1; ring
    calc ((goodX.biUnion (fun x => Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x))).card : ℝ)
        ≤ ((∑ x ∈ goodX, (Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ x ∈ goodX, ((Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x)).card : ℝ) := by
          push_cast
          ring
      _ ≤ ∑ _x ∈ goodX, (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := Finset.sum_le_sum hb
      _ = (goodX.card : ℝ) * (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2:ℝ)^(c*(D:ℝ)^2) * (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := by
          have hc : (goodX.card : ℝ) ≤ (2:ℝ)^(c*(D:ℝ)^2) := by
            calc (goodX.card : ℝ) ≤ ((smallMats γ D).card : ℝ) := by
                  exact_mod_cast Finset.card_filter_le _ _
              _ ≤ (2:ℝ)^(c*(D:ℝ)^2) := hW
          exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by norm_num) _)
  -- total bound on the bad set
  have hBad : (Bad.card : ℝ) ≤ (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) + (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) +
      (2:ℝ)^(c*(D:ℝ)^2) * (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) := by
    have h1 : (Bad.card : ℝ) ≤
        ((((badH ×ˢ (Finset.univ : Finset (Fin r → Fin D → ZMod 2))) ∪
          ((Finset.univ : Finset (Fin r → Fin D → ZMod 2)) ×ˢ badH)).card : ℕ) : ℝ) +
        (((goodX.biUnion (fun x => Finset.univ.filter (fun p : HP => pairCond p.1 p.2 x))).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_union_le _ _
    have h2 : ((((badH ×ˢ (Finset.univ : Finset (Fin r → Fin D → ZMod 2))) ∪
          ((Finset.univ : Finset (Fin r → Fin D → ZMod 2)) ×ˢ badH)).card : ℕ) : ℝ) ≤
        (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) + (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) := by
      have h3 : ((((badH ×ˢ (Finset.univ : Finset (Fin r → Fin D → ZMod 2))) ∪
          ((Finset.univ : Finset (Fin r → Fin D → ZMod 2)) ×ˢ badH)).card : ℕ) : ℝ) ≤
          (((badH ×ˢ (Finset.univ : Finset (Fin r → Fin D → ZMod 2))).card : ℕ) : ℝ) +
          ((((Finset.univ : Finset (Fin r → Fin D → ZMod 2)) ×ˢ badH).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      linarith [hBad1, hBad2]
    linarith [h1, h2, hBad3]
  -- the total number of pairs
  have hTot : ((Finset.univ : Finset HP).card : ℝ) = (2:ℝ)^(2*(r:ℝ)*D) := by
    have := card_univ_hpair r D
    simpa only [HP] using this
  -- final strict inequality
  have hlt : (Bad.card : ℝ) < ((Finset.univ : Finset HP).card : ℝ) := by
    rw [hTot]
    have ha : (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)/8) ≤ (2:ℝ)^(2*(r:ℝ)*D)/4 := by
      have h4 : (2:ℝ)^(2:ℝ) = 4 := by norm_num
      rw [← h4, ← rpow_two_sub, rpow_two_le_iff]
      linarith
    have hc : (2:ℝ)^(c*(D:ℝ)^2) * (2:ℝ)^(2*(r:ℝ)*D - (r:ℝ)^2/4) ≤
        (2:ℝ)^(2*(r:ℝ)*D)/4 := by
      rw [rpow_two_mul]
      have h4 : (2:ℝ)^(2:ℝ) = 4 := by norm_num
      rw [← h4, ← rpow_two_sub, rpow_two_le_iff]
      linarith
    have hX : (0:ℝ) < (2:ℝ)^(2*(r:ℝ)*D) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  -- conclude
  have hex : ∃ p : HP, p ∉ Bad := by
    by_contra h
    push Not at h
    have huniv : Bad = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [huniv] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨p, hp⟩ := hex
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · by_contra hbad
    exact hp (by
      apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; left
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩, Finset.mem_univ _⟩)
  · by_contra hbad
    exact hp (by
      apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩)
  · intro x hx hrx hpc
    exact hp (by
      apply Finset.mem_union.mpr; right
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hrx⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩⟩)


/-- The deterministic step: a pair of codes with distances, property `(*)` and no low-weight
high-rank element of `CA ⊞ CB` is product-expanding. -/
theorem gb_product_expanding {D : ℕ} (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2))
    (α κ : ℝ) (r : ℕ) (hα : 0 < α) (hα1 : α ≤ 1) (hκ : 0 < κ) (hκ8 : κ ≤ α ^ 2 / 8)
    (hdistA : ∀ c ∈ CA, c ≠ 0 → α * D ≤ hammingNorm c)
    (hdistB : ∀ c ∈ CB, c ≠ 0 → α * D ≤ hammingNorm c)
    (hstarA : HasStar α r CA) (hstarB : HasStar α r CB)
    (hnolow : ∀ x ∈ prodSum CA CB, x ≠ 0 → (wt x : ℝ) ≤ 2 * κ * (D : ℝ) ^ 2 → matRank x < r) :
    ProductExpanding κ CA CB := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prodSum x).mp hx
  rcases eq_or_ne (a + b) 0 with hx0 | hx0
  · refine ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, hx0, ?_⟩
    have h0 : nzCols (0 : Fin D × Fin D → ZMod 2) = 0 := by
      simp [nzCols]
    have h1 : nzRows (0 : Fin D × Fin D → ZMod 2) = 0 := by
      simp [nzRows]
    rw [h0, h1]
    simp [wt, hx0]
  · have hxpos : (0:ℝ) < (wt (a + b) : ℝ) := by
      rw [wt]
      exact_mod_cast hammingNorm_pos_iff.mpr hx0
    by_cases hbig : 2 * κ * (D : ℝ) ^ 2 ≤ (wt (a + b) : ℝ)
    · refine ⟨a, ha, b, hb, rfl, ?_⟩
      have h1 : (nzCols a : ℝ) ≤ (D : ℝ) := by exact_mod_cast nzCols_le a
      have h2 : (nzRows b : ℝ) ≤ (D : ℝ) := by exact_mod_cast nzRows_le b
      have h3 : (0:ℝ) ≤ κ * D := by positivity
      calc κ * D * ((nzCols a : ℝ) + (nzRows b : ℝ))
          ≤ κ * D * ((D : ℝ) + (D : ℝ)) := by gcongr
        _ = 2 * κ * (D : ℝ) ^ 2 := by ring
        _ ≤ (wt (a + b) : ℝ) := hbig
    · push Not at hbig
      have hDnn : (0:ℝ) ≤ (D : ℝ) := by positivity
      have hDpos : (0:ℝ) < (D : ℝ) := by
        by_contra hcon
        push Not at hcon
        have hD0 : (D:ℝ) = 0 := le_antisymm hcon hDnn
        rw [hD0] at hbig
        simp at hbig
        linarith
      have hw : (wt (a + b) : ℝ) ≤ α ^ 2 * (D : ℝ) ^ 2 / 4 := by
        have h2κ : 2 * κ ≤ α ^ 2 / 4 := by nlinarith [hκ8, hα, hα1]
        nlinarith [hbig, h2κ, sq_nonneg (D:ℝ)]
      have hr : matRank (a + b) < r :=
        hnolow (a + b) ((mem_prodSum (a+b)).mpr ⟨a, ha, b, hb, rfl⟩) hx0 (le_of_lt hbig)
      obtain ⟨A, B, hzero, hAcard, hBcard⟩ :=
        gb_zero_rect_of_star CA CB α r hα hα1 hstarA hstarB (a + b)
          ((mem_prodSum (a+b)).mpr ⟨a, ha, b, hb, rfl⟩) hx0 hw hr
      have hAB : ∀ c ∈ CA, c ≠ 0 → (Finset.univ \ A).card < hammingNorm c := by
        intro c hc hcne
        have hd := hdistA c hc hcne
        have hhalf : 2 * (wt (a + b) : ℝ) / (α * D) ≤ α * D / 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hw, hα, hDpos, sq_nonneg (D:ℝ)]
        have : (((Finset.univ \ A).card : ℕ) : ℝ) < (hammingNorm c : ℝ) := by
          have hαD : (0:ℝ) < α * D := by positivity
          have hle := hAcard
          nlinarith [hle, hhalf, hd]
        exact_mod_cast this
      have hBB : ∀ c ∈ CB, c ≠ 0 → (Finset.univ \ B).card < hammingNorm c := by
        intro c hc hcne
        have hd := hdistB c hc hcne
        have hhalf : 2 * (wt (a + b) : ℝ) / (α * D) ≤ α * D / 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hw, hα, hDpos, sq_nonneg (D:ℝ)]
        have : (((Finset.univ \ B).card : ℕ) : ℝ) < (hammingNorm c : ℝ) := by
          have hαD : (0:ℝ) < α * D := by positivity
          have hle := hBcard
          nlinarith [hle, hhalf, hd]
        exact_mod_cast this
      obtain ⟨a', ha', b', hb', heq, hnzA, hnzB⟩ :=
        gb_zero_rectangle CA CB (a + b) ((mem_prodSum (a+b)).mpr ⟨a, ha, b, hb, rfl⟩) A B hAB hBB hzero
      refine ⟨a', ha', b', hb', heq, ?_⟩
      have h1 : (nzCols a' : ℝ) ≤ (((Finset.univ \ B).card : ℕ) : ℝ) := by exact_mod_cast hnzA
      have h2 : (nzRows b' : ℝ) ≤ (((Finset.univ \ A).card : ℕ) : ℝ) := by exact_mod_cast hnzB
      have h4κ : 4 * κ ≤ α := by nlinarith [hκ8, hα1, hα]
      calc κ * D * ((nzCols a' : ℝ) + (nzRows b' : ℝ))
          ≤ κ * D * ((((Finset.univ \ B).card : ℕ) : ℝ) + (((Finset.univ \ A).card : ℕ) : ℝ)) := by
            gcongr
        _ ≤ κ * D * (2 * (wt (a + b) : ℝ) / (α * D) + 2 * (wt (a + b) : ℝ) / (α * D)) := by
            gcongr
        _ = 4 * κ * (wt (a + b) : ℝ) / α := by
            field_simp
            ring
        _ ≤ (wt (a + b) : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [h4κ, hxpos]


/-- **Good base codes** (Kalachev–Panteleev, *Two-sided robustly testable codes*, Thm 1 with
`q = 2`, plus KP Lem 1: product-expansion ⇔ agreement testability). For every `r0 < 1` there
are `δ0, κ0 > 0` and `D0` such that for every length `D ≥ D0` some pair of binary codes of rate
`≥ r0` and relative distance `≥ δ0` has `CA ⊗ CB` `κ0`-agreement testable. -/
theorem good_base_code (r0 : ℝ) (hr0 : r0 < 1) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∃ κ0 : ℝ, 0 < κ0 ∧ ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      ∃ CA CB : Submodule (ZMod 2) (Fin D → ZMod 2),
        r0 * D ≤ Module.finrank (ZMod 2) CA ∧ r0 * D ≤ Module.finrank (ZMod 2) CB ∧
        (∀ x ∈ CA, x ≠ 0 → δ0 * D ≤ hammingNorm x) ∧
        (∀ x ∈ CB, x ≠ 0 → δ0 * D ≤ hammingNorm x) ∧
        agreementTestable κ0 CA CB := by
  by_cases h0 : r0 ≤ 0
  · -- degenerate case: the zero code has rate `0 ≥ r0`, and `⊥ ⊗ ⊥ = ⊥` is trivially testable
    refine ⟨1, one_pos, le_refl 1, 1, one_pos, 0, fun D _ => ?_⟩
    refine ⟨⊥, ⊥, ?_, ?_, ?_, ?_, ?_⟩
    · have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
      simp only [finrank_bot]
      push_cast
      nlinarith
    · have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
      simp only [finrank_bot]
      push_cast
      nlinarith
    · intro x hx hxne
      rw [Submodule.mem_bot] at hx
      exact absurd hx hxne
    · intro x hx hxne
      rw [Submodule.mem_bot] at hx
      exact absurd hx hxne
    · intro w1 w2 h1 h2
      have hw1 : w1 = 0 := by
        funext p
        have hp : row w1 p.1 ∈ (⊥ : Submodule (ZMod 2) (Fin D → ZMod 2)) := h1 p.1
        have hz : row w1 p.1 = 0 := by simpa using hp
        simpa [row] using congrFun hz p.2
      have hw2 : w2 = 0 := by
        funext p
        have hp : col w2 p.2 ∈ (⊥ : Submodule (ZMod 2) (Fin D → ZMod 2)) := h2 p.2
        have hz : col w2 p.2 = 0 := by simpa using hp
        simpa [col] using congrFun hz p.1
      refine ⟨0, ?_, ?_⟩
      · rw [tensorCode_eq]
        exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
      · simp [hw1, hw2]
  · push Not at h0
    -- main case `0 < r0 < 1`
    obtain ⟨α, hαpos, hα1, D0a, hsparse⟩ := gb_exists_sparse_param ((1 - r0) / 20) (by linarith)
    obtain ⟨γ, hγpos, D0b, hweight⟩ := gb_exists_weight_param ((1 - r0) ^ 2 / 64)
      (by positivity)
    refine ⟨α, hαpos, hα1, min (α ^ 2 / 8) (γ / 2), lt_min (by positivity) (by positivity),
      max (max D0a D0b) (Nat.ceil (64 / (1 - r0)) + 2), fun D hD => ?_⟩
    have hDa : D0a ≤ D :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
    have hDb : D0b ≤ D :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
    have hDc : Nat.ceil (64 / (1 - r0)) + 2 ≤ D := le_trans (le_max_right _ _) hD
    have hεpos : (0:ℝ) < 1 - r0 := by linarith
    have hεle : (1:ℝ) - r0 ≤ 1 := by linarith
    have hD64 : (64:ℝ) ≤ (1 - r0) * (D:ℝ) := by
      have hceil : (64:ℝ) / (1 - r0) ≤ ((Nat.ceil (64 / (1 - r0)) : ℕ) : ℝ) := Nat.le_ceil _
      have hcast : (((Nat.ceil (64 / (1 - r0)) : ℕ)) : ℝ) + 2 ≤ (D:ℝ) := by
        exact_mod_cast hDc
      rw [div_le_iff₀ hεpos] at hceil
      nlinarith [hceil, hcast, hεpos]
    -- the number `r` of parity checks
    set r : ℕ := Nat.ceil ((1 - r0) * (D:ℝ) / 2) with hrdef
    have hr_ge : (1 - r0) * (D:ℝ) / 2 ≤ (r:ℝ) := by rw [hrdef]; exact Nat.le_ceil _
    have hr_lt : (r:ℝ) < (1 - r0) * (D:ℝ) / 2 + 1 := by
      rw [hrdef]; exact Nat.ceil_lt_add_one (by positivity)
    have hr_le : (r:ℝ) ≤ (1 - r0) * (D:ℝ) := by linarith
    have hr16 : 16 ≤ r := by
      have : (16:ℝ) ≤ (r:ℝ) := by linarith
      exact_mod_cast this
    have hS : ((smallVecs α D).card : ℝ) ≤ (2 : ℝ) ^ (((1 - r0) / 20) * D) := by
      have h1 : smallVecs α D = Finset.univ.filter
          (fun v : Fin D → ZMod 2 => (hammingNorm v : ℝ) ≤ α * D) := by
        ext v
        rw [mem_smallVecs, Finset.mem_filter]
        simp
      rw [h1]
      exact hsparse D hDa
    have hW : ((smallMats γ D).card : ℝ) ≤ (2 : ℝ) ^ (((1 - r0) ^ 2 / 64) * D ^ 2) := by
      have h1 : smallMats γ D = Finset.univ.filter
          (fun x : Fin D × Fin D → ZMod 2 => (hammingNorm x : ℝ) ≤ γ * D ^ 2) := by
        ext v
        rw [mem_smallMats, Finset.mem_filter]
        simp
      rw [h1]
      exact hweight D hDb
    have hr1 : 8 * ((1 - r0) / 20) * (D:ℝ) + 4 ≤ (r:ℝ) := by
      have h2 : 8 * ((1 - r0) / 20) * (D:ℝ) + 4 ≤ (1 - r0) * (D:ℝ) / 2 := by
        nlinarith [hD64]
      linarith [hr_ge]
    have hr3 : (1 - r0) ^ 2 / 64 * (D:ℝ) ^ 2 + 2 ≤ (r:ℝ) ^ 2 / 4 := by
      have h1 : ((1 - r0) * (D:ℝ) / 2) ^ 2 ≤ (r:ℝ) ^ 2 := by
        have h2 : (0:ℝ) ≤ (1 - r0) * (D:ℝ) / 2 := by positivity
        nlinarith [hr_ge]
      nlinarith [h1, hD64]
    obtain ⟨H1, H2, hstar1, hstar2, hnonlow⟩ :=
      gb_exists_good_pair (D := D) (r := r) (α := α) (γ := γ) ((1 - r0) / 20)
        ((1 - r0) ^ 2 / 64) hαpos hS hW hr1 hr16 hr3
    refine ⟨kerCode H1, kerCode H2, ?_, ?_, ?_, ?_, ?_⟩
    · -- rate
      have h1 : D ≤ r + frk (kerCode H1) := gb_finrank_kerCode H1
      have h2 : D - r ≤ frk (kerCode H1) := by omega
      have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
      have hrD : (r:ℝ) ≤ (D:ℝ) := by nlinarith [hr_le, hεle, hDnn]
      have hrDnat : r ≤ D := by exact_mod_cast hrD
      have hcast : ((D - r : ℕ) : ℝ) = (D:ℝ) - (r:ℝ) := by
        rw [Nat.cast_sub hrDnat]
      have : r0 * (D:ℝ) ≤ ((D - r : ℕ) : ℝ) := by
        rw [hcast]
        nlinarith [hr_le]
      calc r0 * (D:ℝ) ≤ ((D - r : ℕ) : ℝ) := this
        _ ≤ (Module.finrank (ZMod 2) (kerCode H1) : ℝ) := by
            rw [show Module.finrank (ZMod 2) (kerCode H1) = frk (kerCode H1) from rfl]
            exact_mod_cast h2
    · -- rate, second code
      have h1 : D ≤ r + frk (kerCode H2) := gb_finrank_kerCode H2
      have h2 : D - r ≤ frk (kerCode H2) := by omega
      have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
      have hrD : (r:ℝ) ≤ (D:ℝ) := by nlinarith [hr_le, hεle, hDnn]
      have hrDnat : r ≤ D := by exact_mod_cast hrD
      have hcast : ((D - r : ℕ) : ℝ) = (D:ℝ) - (r:ℝ) := by
        rw [Nat.cast_sub hrDnat]
      have : r0 * (D:ℝ) ≤ ((D - r : ℕ) : ℝ) := by
        rw [hcast]
        nlinarith [hr_le]
      calc r0 * (D:ℝ) ≤ ((D - r : ℕ) : ℝ) := this
        _ ≤ (Module.finrank (ZMod 2) (kerCode H2) : ℝ) := by
            rw [show Module.finrank (ZMod 2) (kerCode H2) = frk (kerCode H2) from rfl]
            exact_mod_cast h2
    · exact gb_dist_of_hasStar hαpos (le_trans (by norm_num) hr16) hstar1
    · exact gb_dist_of_hasStar hαpos (le_trans (by norm_num) hr16) hstar2
    · -- agreement testability via product expansion
      refine gb_agreement_of_prodExp (min (α ^ 2 / 8) (γ / 2)) (kerCode H1) (kerCode H2) ?_
      refine gb_product_expanding (kerCode H1) (kerCode H2) α (min (α ^ 2 / 8) (γ / 2)) r
        hαpos hα1 (lt_min (by positivity) (by positivity)) (min_le_left _ _)
        (gb_dist_of_hasStar hαpos (le_trans (by norm_num) hr16) hstar1)
        (gb_dist_of_hasStar hαpos (le_trans (by norm_num) hr16) hstar2) hstar1 hstar2 ?_
      intro x hx hxne hw
      by_contra hcon
      push Not at hcon
      have hmem : x ∈ smallMats γ D := by
        rw [mem_smallMats]
        have hmin : 2 * min (α ^ 2 / 8) (γ / 2) ≤ γ := by
          have := min_le_right (α ^ 2 / 8) (γ / 2)
          linarith
        have hw' : (hammingNorm x : ℝ) ≤ 2 * min (α ^ 2 / 8) (γ / 2) * (D:ℝ) ^ 2 := hw
        push_cast
        nlinarith [hw', hmin, sq_nonneg (D:ℝ)]
      exact hnonlow x hmem hcon (gb_prodSum_pairCond H1 H2 x hx)

end Work.LT

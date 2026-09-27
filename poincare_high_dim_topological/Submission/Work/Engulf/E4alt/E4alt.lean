import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.exists_normData
import Submission.Work.Engulf.E4alt.exists_core_margin
import Submission.Work.Engulf.E4S.All
import Submission.Work.Engulf.Chain.E4Skel

/-!
# `Work.Engulf.E4alt.E4alt` — Newman's Lemma 7, Case 1 (second proof)

The assembly of the `E4` argument from
* the normalisation `Work.Engulf.E4alt.exists_normData` (giving `NormData` + `Core11` + `CarrierS`),
* the core margin `Work.Engulf.E4alt.exists_core_margin`,
* the per-simplex step `Work.Engulf.E4S.stepG` of the shelling loop with a **moving** map
  (invariant `Work.Engulf.Alt.AltInnerG`), and
* the closing step `Work.Engulf.Chain.engulfs_of_Skel` (`topOf ⊆ q-skeleton`).

Budget: the normalisation is run with `ε / 2`, and the loop budget is
`β := min (ε / 2 - η) μ / (ord.length + 1)`, so that `ord.length * β + η < ε / 2` and hence the
final map is within `ε / 2 + ε / 2 = ε` of `f`.  See `Submission/Work/NOTES_LEAD_poincare_E4c.md`.
-/

open Set Metric PL

namespace Work.Engulf.E4alt

universe u

/-- `L7c` follows from `B q` (Newman's Lemma 7, Case 1, §§12–14). -/
theorem E4alt (n p q : ℕ) (T : Work.Engulf.ToolsAll.{u} n) (hq : q + 1 ≤ p + 1)
    (hB : Work.Engulf.B.{u} n p q) : Work.Engulf.L7c.{u} n p q := by
  intro M inst V X N Γ K L f τ₀ τ₁ ψ A H7 SCh hch ε hε
  -- half the budget for the normalisation
  set ε₂ : ℝ := ε / 2 with hε₂def
  have hε₂ : 0 < ε₂ := by rw [hε₂def]; linarith
  obtain ⟨ND, hc11, hcS⟩ :=
    Work.Engulf.E4alt.exists_normData n p q T hq A H7 SCh hch ε₂ hε₂
  obtain ⟨μ, hμpos, hmarg⟩ := Work.Engulf.E4alt.exists_core_margin ND
  -- the loop budget
  set len : ℝ := (ND.ord.length : ℝ) with hlendef
  have hlen0 : 0 ≤ len := by rw [hlendef]; positivity
  have hden : 0 < len + 1 := by linarith
  set β : ℝ := min (ε₂ - ND.η) μ / (len + 1) with hβdef
  have hminpos : 0 < min (ε₂ - ND.η) μ := lt_min (by linarith [ND.hηε]) hμpos
  have hβpos : 0 < β := by rw [hβdef]; exact div_pos hminpos hden
  have hβμ : len * β < μ := by
    have h1 : β ≤ μ / (len + 1) := by
      rw [hβdef]
      exact div_le_div_of_nonneg_right (min_le_right _ _) hden.le
    have h2 : len * (μ / (len + 1)) < μ := by
      have hlt : len / (len + 1) < 1 := by
        rw [div_lt_one hden]; linarith
      calc len * (μ / (len + 1)) = (len / (len + 1)) * μ := by ring
        _ < 1 * μ := mul_lt_mul_of_pos_right hlt hμpos
        _ = μ := one_mul _
    nlinarith [h1, h2, hlen0, hμpos]
  have hβε : len * β + ND.η < ε₂ := by
    have h1 : β ≤ (ε₂ - ND.η) / (len + 1) := by
      rw [hβdef]
      exact div_le_div_of_nonneg_right (min_le_left _ _) hden.le
    have hpos : 0 < ε₂ - ND.η := by linarith [ND.hηε]
    have h2 : len * ((ε₂ - ND.η) / (len + 1)) < ε₂ - ND.η := by
      have hlt : len / (len + 1) < 1 := by
        rw [div_lt_one hden]; linarith
      calc len * ((ε₂ - ND.η) / (len + 1)) = (len / (len + 1)) * (ε₂ - ND.η) := by ring
        _ < 1 * (ε₂ - ND.η) := mul_lt_mul_of_pos_right hlt hpos
        _ = ε₂ - ND.η := one_mul _
    nlinarith [h1, h2, hlen0, hpos]
  -- the loop
  have hloop : ∀ i, i ≤ ND.ord.length → ∃ (g : PL.E N → M) (h : M ≃ₜ M),
      Work.Engulf.Alt.AltInnerG V X K L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ND.Γ₁ ND.g₁
        ND.ord β i g h := by
    intro i
    induction i with
    | zero => intro _; exact ⟨ND.g₁, Homeomorph.refl M, Work.Engulf.E4S.altInnerG_zero ND _⟩
    | succ i ih =>
      intro hle
      have hi : i ≤ ND.ord.length := Nat.le_of_succ_le hle
      obtain ⟨g, h, inv⟩ := ih hi
      have hilt : i < ND.ord.length := Nat.lt_of_succ_le hle
      exact Work.Engulf.E4S.stepG T hB hq A H7 SCh hch hε₂ ND hc11 hcS hmarg hβpos hβμ hilt inv
  obtain ⟨g, h, inv⟩ := hloop ND.ord.length le_rfl
  -- the map `g` is close to `f` and equal to it on `L`
  have hg_frz : Set.EqOn g f L := fun x hx => (inv.frz (Or.inl hx)).trans (ND.g₁frz hx)
  have hg_near : ∀ x ∈ ND.Γ₁.space, dist (g x) (f x) < ε₂ := by
    intro x hx
    have h1 : dist (g x) (ND.g₁ x) ≤ len * β := by
      rw [hlendef]; exact inv.near x hx
    have h2 : dist (ND.g₁ x) (f x) < ND.η := ND.g₁near x hx
    linarith [dist_triangle (g x) (ND.g₁ x) (f x)]
  -- the engulfing at level `Γ₁` and the closing step
  have hcov : Work.Engulf.topOf τ₀ τ₁ ⊆ Work.Engulf.Chain.Skel ND.ord :=
    Work.Engulf.Chain.topOf_subset_Skel ND.ord
      ⟨H7.ne₀.choose, Finset.mem_union_left τ₁ H7.ne₀.choose_spec⟩
      (Γ.indep H7.mem) ND.ord_mem ND.ord_sub ND.ord_card ND.ord_cov
  have hEng₁ : Work.Engulf.Engulfs V X ND.Γ₁ (K ∪ Work.Engulf.Chain.Skel ND.ord) L g ε₂ :=
    ⟨g, inv.cont, fun x _ => rfl, fun x _ => by simpa using hε₂, h, inv.supp, inv.eng⟩
  have hEng₂ : Work.Engulf.Engulfs V X Γ (K ∪ Work.Engulf.topOf τ₀ τ₁) L g ε₂ :=
    Work.Engulf.Chain.engulfs_of_Skel ND.sub ND.ord hcov hEng₁
  -- replace the base map `g` by `f` and double the budget
  obtain ⟨g₀, hg₀c, hg₀L, hg₀d, h₀, h₀sup, h₀eng⟩ := hEng₂
  refine ⟨g₀, hg₀c, hg₀L.trans hg_frz, ?_, h₀, h₀sup, h₀eng⟩
  intro x hx
  have hx₁ : x ∈ ND.Γ₁.space := ND.sub.1 ▸ hx
  have h1 : dist (g₀ x) (g x) < ε₂ := hg₀d x (ND.sub.1 ▸ hx)
  have h2 : dist (g x) (f x) < ε₂ := hg_near x hx₁
  have h3 : dist (g₀ x) (f x) ≤ dist (g₀ x) (g x) + dist (g x) (f x) :=
    dist_triangle _ _ _
  have h4 : ε₂ + ε₂ = ε := by rw [hε₂def]; ring
  linarith

end Work.Engulf.E4alt

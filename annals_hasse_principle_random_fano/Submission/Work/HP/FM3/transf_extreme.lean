import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Transf.indep_of_le_finrank
import Submission.Work.HP.FM3.basic
import Submission.Work.HP.FM3.covering_parallelepiped
import Submission.Work.HP.FM3.dot_image_zmultiples
import Submission.Work.HP.FM3.rank_secLat_add_one
import Submission.Work.HP.FM3.section_dual_lamR_ge
import Submission.Work.HP.FM3.dualLat_ne_bot

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

/-- The constant `√7/4` produced by the transference step `section_dual_lamR_ge`. -/
private def C0 : ℝ := Real.sqrt 7 / 4

private lemma C0_pos : 0 < C0 := by
  rw [C0]; positivity

/-- The recursive constant: `D m` bounds `λ_i(L)·λ₁(dualLat L)` for all `i ≤ m` and all discrete
`ℤ`-submodules `L ⊆ ℝ^ι` of real rank `m`. -/
private def D : ℕ → ℝ
  | 0 => 1
  | (m + 1) => max (D m / C0) (Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1)) + 1

private lemma D_zero : D 0 = 1 := rfl

private lemma D_succ (m : ℕ) :
    D (m + 1) = max (D m / C0) (Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1)) + 1 := rfl

private lemma D_pos : ∀ m, 0 < D m
  | 0 => by rw [D_zero]; norm_num
  | (m + 1) => by
      rw [D_succ]
      have h1 : 0 < D m / C0 := div_pos (D_pos m) C0_pos
      have h2 : 0 < max (D m / C0) (Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1)) :=
        lt_of_lt_of_le h1 (le_max_left _ _)
      linarith


/-- The induction.  For every `m`, every discrete `ℤ`-submodule `L ⊆ ℝ^ι` of real rank `m` and
every `i ≤ m` there are `i` linearly independent vectors of `L` whose norms are bounded by
`D m / λ₁(dualLat L)`. -/
private theorem main_aux : ∀ m : ℕ, ∀ (L : Submodule ℤ (ι → ℝ)), DiscreteTopology ↥L →
    rkR L = m → ∀ i ≤ m, ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧
      ∀ j, rNorm (f j) * lamR (dualLat L) 1 ≤ D m := by
  intro m
  induction m with
  | zero =>
      intro L _ hrk i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      exact ⟨fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  | succ m ih =>
      intro L hL hrk i hi
      by_cases hlam : lamR (dualLat L) 1 = 0
      · obtain ⟨f, hfL, hfI⟩ := indep_of_le_finrank L (k := i) (by rw [hrk]; exact hi)
        exact ⟨f, hfL, hfI, fun j => by rw [hlam, mul_zero]; exact (D_pos (m + 1)).le⟩
      · have hlam_pos : 0 < lamR (dualLat L) 1 :=
          lt_of_le_of_ne (lamR_nonneg (dualLat L) 1) (Ne.symm hlam)
        -- a short dual vector
        have hneDual : ∃ v ∈ dualLat L, v ≠ 0 := by
          by_contra hc
          push Not at hc
          have hbot : dualLat L = ⊥ := (Submodule.eq_bot_iff _).mpr fun x hx => hc x hx
          rw [hbot, lamR_eq_zero_of_all_zero ⊥ (fun v hv => (Submodule.mem_bot ℤ).mp hv)] at hlam
          exact hlam rfl
        obtain ⟨v, hv, hv0, hvb⟩ := exists_norm_le_of_lamR_lt (dualLat L) hneDual
          (show lamR (dualLat L) 1 < (3 / 2) * lamR (dualLat L) 1 by linarith)
        have hne_dot : ∃ z ∈ L, dotR v z ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hv0 (dotR_eq_zero_of_forall_mem (L := L) hc hv.1)
        obtain ⟨d, hdpos, ⟨w, hw, hwd⟩, hdiv⟩ := dot_image_zmultiples L v hv hne_dot
        -- normalise: `d = 1`
        have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
        have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
        have hmem : (d : ℝ)⁻¹ • v ∈ dualLat L := by
          refine ⟨Submodule.smul_mem _ _ hv.1, fun z hz => ?_⟩
          obtain ⟨k, hk⟩ := hdiv z hz
          refine ⟨k, ?_⟩
          show dotR ((d : ℝ)⁻¹ • v) z = (k : ℝ)
          rw [dotR_smul_left, hk]
          field_simp
        have hd1 : d = 1 := by
          have hne0 : (d : ℝ)⁻¹ • v ≠ 0 := by
            intro h
            rcases smul_eq_zero.mp h with h1 | h1
            · exact hdne (inv_eq_zero.mp h1)
            · exact hv0 h1
          have hle : lamR (dualLat L) 1 ≤ rNorm ((d : ℝ)⁻¹ • v) :=
            lamR_le_rNorm _ hmem hne0
          rw [rNorm_smul, abs_of_pos (inv_pos.mpr hdposR)] at hle
          have h3 : (d : ℝ) * lamR (dualLat L) 1 ≤ (3 / 2) * lamR (dualLat L) 1 := by
            have h2 : (d : ℝ) * ((d : ℝ)⁻¹ * rNorm v) = rNorm v := by
              field_simp
            calc (d : ℝ) * lamR (dualLat L) 1 ≤ (d : ℝ) * ((d : ℝ)⁻¹ * rNorm v) :=
                  mul_le_mul_of_nonneg_left hle hdposR.le
              _ = rNorm v := h2
              _ ≤ (3 / 2) * lamR (dualLat L) 1 := hvb
          have hd32 : (d : ℝ) ≤ 3 / 2 := le_of_mul_le_mul_right h3 hlam_pos
          have hdlt : d < 2 := by exact_mod_cast (by linarith : (d : ℝ) < 2)
          omega
        have hwv : dotR v w = 1 := by rw [hwd, hd1]; norm_num
        -- the section
        have hdisc0 : DiscreteTopology ↥(secLat v L) := secLat_discrete L hL v
        have hrk0 : rkR (secLat v L) = m := by
          have h := rank_secLat_add_one L v w hv hw hwv
          rw [hrk] at h
          omega
        have hsec_le : secLat v L ≤ L := secLat_le v L
        have hperp : ∀ y ∈ Submodule.span ℝ (secLat v L : Set (ι → ℝ)), dotR v y = 0 := by
          intro y hy
          refine Submodule.span_induction (p := fun z _ => dotR v z = 0) (fun z hz => hz.2) ?_ ?_ ?_ hy
          · simp
          · intro a b _ _ ha hb; rw [dotR_add_right, ha, hb, add_zero]
          · intro c a _ ha; rw [dotR_smul_right, ha, mul_zero]
        -- the bound coming from the transference step on the section
        have hbound0 : ∀ (hm : 1 ≤ m), C0 * lamR (dualLat L) 1 ≤ lamR (dualLat (secLat v L)) 1 :=
          fun hm => Work.HP.Vero.le_lamR_one (dualLat (secLat v L))
            (dualLat_ne_bot_of_discrete (secLat v L) hdisc0 (by rw [hrk0]; exact hm))
            (fun u hu hu0 => section_dual_lamR_ge L v w hv hv0 hw hwv hvb u hu hu0)
        by_cases hi_le : i ≤ m
        · by_cases hm0 : m = 0
          · subst hm0
            have hi0 : i = 0 := by omega
            subst hi0
            exact ⟨fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type,
              fun j => j.elim0⟩
          · have hm1 : 1 ≤ m := by omega
            have hC0le := hbound0 hm1
            obtain ⟨f, hfL, hfI, hfb⟩ := ih (secLat v L) hdisc0 hrk0 i hi_le
            refine ⟨f, fun j => hsec_le (hfL j), hfI, fun j => ?_⟩
            have hlam_le : lamR (dualLat L) 1 ≤ lamR (dualLat (secLat v L)) 1 / C0 := by
              rw [le_div_iff₀ C0_pos]
              linarith [hC0le]
            calc rNorm (f j) * lamR (dualLat L) 1
                ≤ rNorm (f j) * (lamR (dualLat (secLat v L)) 1 / C0) :=
                  mul_le_mul_of_nonneg_left hlam_le (rNorm_nonneg _)
              _ = rNorm (f j) * lamR (dualLat (secLat v L)) 1 / C0 := by ring
              _ ≤ D m / C0 := div_le_div_of_nonneg_right (hfb j) C0_pos.le
              _ ≤ D (m + 1) := by
                  rw [D_succ]
                  linarith [le_max_left (D m / C0)
                    (Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1))]
        · have hi_eq : i = m + 1 := by omega
          subst hi_eq
          obtain ⟨b, hbL, hbLI, hbb⟩ := ih (secLat v L) hdisc0 hrk0 m le_rfl
          have hvnorm_ne : rNorm v ≠ 0 := fun h => hv0 (rNorm_eq_zero_iff.mp h)
          have hv2ne : (rNorm v) ^ 2 ≠ 0 := pow_ne_zero 2 hvnorm_ne
          have hv2pos : 0 < (rNorm v) ^ 2 := pow_pos (rNorm_pos_iff.mpr hv0) 2
          -- the base point `p0 = w - (1/‖v‖²) v`
          set p0 : ι → ℝ := w - ((rNorm v) ^ 2)⁻¹ • v with hp0def
          have hp0v : dotR v p0 = 0 := by
            rw [hp0def, dotR_sub_right, dotR_smul_right, hwv, ← rNorm_sq]
            field_simp
            ring
          have hp0span : p0 ∈ Submodule.span ℝ (L : Set (ι → ℝ)) := by
            rw [hp0def]
            exact Submodule.sub_mem _ (Submodule.subset_span hw) (Submodule.smul_mem _ _ hv.1)
          have hp0sec : p0 ∈ Submodule.span ℝ (secLat v L : Set (ι → ℝ)) := by
            have key2 : ∀ x ∈ Submodule.span ℝ (L : Set (ι → ℝ)), ∃ t : ℝ,
                x - t • w ∈ Submodule.span ℝ (secLat v L : Set (ι → ℝ)) := by
              intro x hx
              refine Submodule.span_induction (p := fun y _ => ∃ t : ℝ,
                y - t • w ∈ Submodule.span ℝ (secLat v L : Set (ι → ℝ))) ?_ ?_ ?_ ?_ hx
              · intro z hz
                obtain ⟨k, hk⟩ := hv.2 z hz
                refine ⟨(k : ℝ), ?_⟩
                have hmemz : z - k • w ∈ secLat v L := by
                  refine ⟨Submodule.sub_mem _ hz (Submodule.smul_mem _ _ hw), ?_⟩
                  show dotR v (z - k • w) = 0
                  rw [← Int.cast_smul_eq_zsmul ℝ k w, dotR_sub_right, dotR_smul_right, hwv,
                    mul_one]
                  rw [show dotR v z = (k : ℝ) from hk, sub_self]
                rw [Int.cast_smul_eq_zsmul ℝ k w]
                exact Submodule.subset_span hmemz
              · exact ⟨0, by simp⟩
              · intro a c _ _ ha hc
                obtain ⟨t1, ht1⟩ := ha
                obtain ⟨t2, ht2⟩ := hc
                refine ⟨t1 + t2, ?_⟩
                have heq : a + c - (t1 + t2) • w = (a - t1 • w) + (c - t2 • w) := by module
                rw [heq]
                exact Submodule.add_mem _ ht1 ht2
              · intro c a _ ha
                obtain ⟨t, ht⟩ := ha
                refine ⟨c * t, ?_⟩
                have heq : c • a - (c * t) • w = c • (a - t • w) := by module
                rw [heq]
                exact Submodule.smul_mem _ _ ht
            obtain ⟨t, ht⟩ := key2 p0 hp0span
            have ht0 : t = 0 := by
              have h1 := hperp _ ht
              rw [dotR_sub_right, dotR_smul_right, hwv, mul_one, hp0v] at h1
              linarith
            rwa [ht0, zero_smul, sub_zero] at ht
          -- covering
          obtain ⟨z, hz, hzcov⟩ :=
            covering_parallelepiped (secLat v L) m hrk0 b hbL hbLI p0 hp0sec
          have hsum : ∑ j : Fin m, rNorm (b j) ≤ (m : ℝ) * D m / (C0 * lamR (dualLat L) 1) := by
            by_cases hm0 : m = 0
            · subst hm0; simp
            · have hm1 : 1 ≤ m := by omega
              have hC0le := hbound0 hm1
              have hlam0pos : 0 < lamR (dualLat (secLat v L)) 1 :=
                lt_of_lt_of_le (mul_pos C0_pos hlam_pos) hC0le
              calc ∑ j : Fin m, rNorm (b j)
                  ≤ ∑ _j : Fin m, D m / lamR (dualLat (secLat v L)) 1 := by
                    refine Finset.sum_le_sum fun j _ => ?_
                    rw [le_div_iff₀ hlam0pos]
                    exact hbb j
                _ = (m : ℝ) * (D m / lamR (dualLat (secLat v L)) 1) := by
                    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
                _ ≤ (m : ℝ) * (D m / (C0 * lamR (dualLat L) 1)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
                    exact div_le_div_of_nonneg_left (D_pos m).le (mul_pos C0_pos hlam_pos) hC0le
                _ = (m : ℝ) * D m / (C0 * lamR (dualLat L) 1) := by ring
          have hmu : rNorm (p0 - z) ≤ ((m : ℝ) * D m / (2 * C0)) / lamR (dualLat L) 1 := by
            have h1 : (1 / 2) * ((m : ℝ) * D m / (C0 * lamR (dualLat L) 1))
                = ((m : ℝ) * D m / (2 * C0)) / lamR (dualLat L) 1 := by ring
            calc rNorm (p0 - z) ≤ (1 / 2) * ∑ j : Fin m, rNorm (b j) := hzcov
              _ ≤ (1 / 2) * ((m : ℝ) * D m / (C0 * lamR (dualLat L) 1)) :=
                  mul_le_mul_of_nonneg_left hsum (by norm_num)
              _ = ((m : ℝ) * D m / (2 * C0)) / lamR (dualLat L) 1 := h1
          -- the extra vector
          set wq : ι → ℝ := w - z with hwqdef
          have hwqL : wq ∈ L := by
            rw [hwqdef]; exact Submodule.sub_mem _ hw hz.1
          have hwqv : dotR v wq = 1 := by
            rw [hwqdef, dotR_sub_right, hwv, hz.2, sub_zero]
          have hdecomp : wq = (p0 - z) + ((rNorm v) ^ 2)⁻¹ • v := by
            rw [hwqdef, hp0def]; module
          have horth : dotR (p0 - z) (((rNorm v) ^ 2)⁻¹ • v) = 0 := by
            rw [dotR_smul_right, dotR_sub_left, dotR_comm p0 v, hp0v, dotR_comm z v, hz.2,
              sub_zero, mul_zero]
          have hsq : rNorm wq ^ 2 = rNorm (p0 - z) ^ 2 + 1 / (rNorm v) ^ 2 := by
            rw [hdecomp, rNorm_add_sq_of_orthogonal horth, rNorm_smul,
              abs_of_pos (inv_pos.mpr hv2pos)]
            field_simp
          have hvge : lamR (dualLat L) 1 ≤ rNorm v := lamR_le_rNorm (dualLat L) hv hv0
          have hsq2 : (rNorm wq * lamR (dualLat L) 1) ^ 2 ≤
              ((m : ℝ) * D m / (2 * C0)) ^ 2 + 1 := by
            have h1 : rNorm (p0 - z) * lamR (dualLat L) 1 ≤ (m : ℝ) * D m / (2 * C0) :=
              (le_div_iff₀ hlam_pos).mp hmu
            have h2 : rNorm (p0 - z) ^ 2 * (lamR (dualLat L) 1) ^ 2 ≤
                ((m : ℝ) * D m / (2 * C0)) ^ 2 := by
              rw [← mul_pow]
              exact pow_le_pow_left₀ (mul_nonneg (rNorm_nonneg _) hlam_pos.le) h1 2
            have h3 : (1 / (rNorm v) ^ 2) * (lamR (dualLat L) 1) ^ 2 ≤ 1 := by
              rw [div_mul_eq_mul_div, one_mul, div_le_one hv2pos]
              exact pow_le_pow_left₀ (lamR_nonneg _ _) hvge 2
            rw [mul_pow, hsq]
            linarith
          have hfinal : rNorm wq * lamR (dualLat L) 1 ≤ D (m + 1) := by
            have h4 : rNorm wq * lamR (dualLat L) 1 ≤
                Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1) :=
              (Real.le_sqrt (mul_nonneg (rNorm_nonneg _) hlam_pos.le)
                (by positivity)).mpr hsq2
            rw [D_succ]
            linarith [le_max_right (D m / C0) (Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1))]
          -- assemble
          refine ⟨Fin.snoc b wq, fun j => ?_, ?_, fun j => ?_⟩
          · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
            · rw [Fin.snoc_castSucc]; exact hsec_le (hbL k)
            · rw [Fin.snoc_last]; exact hwqL
          · refine LinearIndependent.finSnoc hbLI ?_
            intro hmemq
            have h1 : dotR v wq = 0 := hperp wq (Submodule.span_mono ?_ hmemq)
            · rw [hwqv] at h1; exact one_ne_zero h1
            · rintro y ⟨k, rfl⟩; exact hbL k
          · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
            · rw [Fin.snoc_castSucc]
              by_cases hm0 : m = 0
              · subst hm0; exact k.elim0
              · have hm1 : 1 ≤ m := by omega
                have hC0le := hbound0 hm1
                have hlam_le : lamR (dualLat L) 1 ≤ lamR (dualLat (secLat v L)) 1 / C0 := by
                  rw [le_div_iff₀ C0_pos]
                  linarith [hC0le]
                calc rNorm (b k) * lamR (dualLat L) 1
                    ≤ rNorm (b k) * (lamR (dualLat (secLat v L)) 1 / C0) :=
                      mul_le_mul_of_nonneg_left hlam_le (rNorm_nonneg _)
                  _ = rNorm (b k) * lamR (dualLat (secLat v L)) 1 / C0 := by ring
                  _ ≤ D m / C0 := div_le_div_of_nonneg_right (hbb k) C0_pos.le
                  _ ≤ D (m + 1) := by
                      rw [D_succ]
                      linarith [le_max_left (D m / C0)
                        (Real.sqrt (((m : ℝ) * D m / (2 * C0)) ^ 2 + 1))]
            · rw [Fin.snoc_last]; exact hfinal

theorem transf_extreme {ι : Type*} [Fintype ι] (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℝ)), DiscreteTopology ↥L →
      r ≤ Module.finrank ℝ (Submodule.span ℝ (L : Set (ι → ℝ))) →
      ∃ f : Fin r → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧
        ∀ j, rNorm (f j) * lamR (dualLat L) 1 ≤ C := by
  refine ⟨∑ k ∈ Finset.range (Fintype.card ι + 1), D k + 1, ?_, ?_⟩
  · refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun k _ => (D_pos k).le) zero_lt_one
  · intro L hL hr
    obtain ⟨f, hfL, hfI, hfb⟩ := main_aux (rkR L) L hL rfl r hr
    refine ⟨f, hfL, hfI, fun j => ?_⟩
    refine (hfb j).trans ?_
    have hle : D (rkR L) ≤ ∑ k ∈ Finset.range (Fintype.card ι + 1), D k :=
      Finset.single_le_sum (fun k _ => (D_pos k).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (rkR_le_card L)))
    linarith

end Work.HP.FM3

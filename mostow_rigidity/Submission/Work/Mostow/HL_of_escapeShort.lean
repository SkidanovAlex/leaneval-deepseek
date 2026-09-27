import Mathlib
import Submission.Mostow.HLDefs
import Submission.Work.Mostow.HLlinks
import Submission.Work.Mostow.Margulis.nearId_conj_power_parametric
import Submission.Work.Mostow.near1_unitBall
import Submission.Work.Mostow.escape_of_horoball
import Submission.Work.Mostow.no_fixed_of_orderOf_zero

set_option maxHeartbeats 1000000

/-! Guidance from the project lead (the requester):

# HL_of_escapeShort (lead's design) — HL WITHOUT bounded torsion
Same assembly as HL_of_boundedTorsion (read REFS/lead-design/NOTES_LEAD_HLroute.md §"HL_of_boundedTorsion"), but the
near-identity NON-ELLIPTIC element at z_t = sinh t • ζ comes from hesc (GAP-A) instead of hgap + hthin:
 1. z_t escapes every Γ•K: hdist z_t (γ•0) ≥ t + s − C (busemann 1-Lipschitz, busemann ζ z_t = −t, orbit-free) and
    K ⊆ closedBall 0 r ⇒ hdist z_t (γ•k) ≥ hdist z_t (γ•0) − r.
 2. hesc ⇒ g_t ∈ Γ of infinite order with hdist z_t (g_t z_t) < ε.
 3. Dirichlet power: ∀ η ∃ M(η) ε(η): an infinite-order g that is ε(η)-short at z has a power g^m, 1 ≤ m ≤ M(η), with
    NearIdAt g^m z η (boost z to 0; pigeonhole on the rotation parts of g, g², …, g^{M}; translations ≤ M·ε). g^m has
    infinite order ⇒ no fixed point (finite point stabilisers in a discrete group) ⇒ ClassifyProp applies.
 4. Continue exactly as in HL_of_boundedTorsion from "Links" on.
-/


namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Filter

noncomputable section

variable {n : ℕ}

/-! ### Placeholders for the delegated helper lemmas (to be replaced by imports) -/

/-! ### Elementaries -/

/-- Powers of an element of infinite order have infinite order. -/
lemma orderOf_pow_eq_zero {G : Type*} [Group G] (g : G) {m : ℕ} (hm : 0 < m)
    (hg : orderOf g = 0) : orderOf (g ^ m) = 0 := by
  by_contra h
  have hk : 0 < orderOf (g ^ m) := Nat.pos_of_ne_zero h
  have h1 : (g ^ m) ^ orderOf (g ^ m) = 1 := pow_orderOf_eq_one _
  have h2 : g ^ (m * orderOf (g ^ m)) = 1 := by rw [pow_mul]; exact h1
  have h3 : orderOf g ∣ m * orderOf (g ^ m) := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hg] at h3
  have h4 : m * orderOf (g ^ m) = 0 := Nat.eq_zero_of_zero_dvd h3
  rcases Nat.mul_eq_zero.mp h4 with h5 | h5
  · omega
  · exact h h5

/-! ### Near-identity powers at an arbitrary point -/

/-- The parametric pigeonhole of `Margulis.nearId_conj_power_parametric` upgraded to the
neighbourhood form `NearIdAt`. -/
theorem nearIdAt_of_short (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ (M : ℕ) (ε : ℝ), 0 < M ∧ 0 < ε ∧
      ∀ (z : E n) (g : PO n 1), hdist z (g • z) < ε →
        ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧ NearIdAt (g ^ m) z η := by
  intro η hη
  have hP : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨q, hqpos, hq⟩ := near1_unitBall n hA hI η hη
  obtain ⟨N, δ, hδ, hN, hmain⟩ := Margulis.nearId_conj_power_parametric n hA hI q hqpos
  refine ⟨N, δ, hN, hδ, ?_⟩
  intro z g hg
  obtain ⟨h, hh0, hhall⟩ := hmain z
  obtain ⟨m, hm1, hmN, hNear⟩ := hhall g hg
  refine ⟨m, hm1, hmN, ?_⟩
  obtain ⟨A, hAcoe, hA1⟩ := hNear
  intro u hu
  have hw : h • (h⁻¹ • u) = u := by rw [← hP.mul_smul, mul_inv_cancel, hP.one_smul]
  have hwle : hdist (0 : E n) (h⁻¹ • u) ≤ 1 := by
    have h1 := hId.isom_smul h (0 : E n) (h⁻¹ • u)
    rw [hh0, hw] at h1
    rw [← h1]; exact hu
  have h2 : hdist (h⁻¹ • u) ((A : PO n 1) • (h⁻¹ • u)) < η := hq A (h⁻¹ • u) hA1 hwle
  have hgm : (g ^ m) • (h • (h⁻¹ • u)) = h • ((h⁻¹ * g ^ m * h) • (h⁻¹ • u)) := by
    have h1 : (g ^ m) • (h • (h⁻¹ • u)) = ((g ^ m) * h) • (h⁻¹ • u) :=
      (hP.mul_smul (g ^ m) h (h⁻¹ • u)).symm
    have h2 : h • ((h⁻¹ * g ^ m * h) • (h⁻¹ • u)) =
        (h * (h⁻¹ * g ^ m * h)) • (h⁻¹ • u) :=
      (hP.mul_smul h (h⁻¹ * g ^ m * h) (h⁻¹ • u)).symm
    have heq : (g ^ m) * h = h * (h⁻¹ * g ^ m * h) := by group
    rw [h1, h2, heq]
  have hkey : hdist u ((g ^ m) • u) = hdist (h⁻¹ • u) ((A : PO n 1) • (h⁻¹ • u)) := by
    have hstep1 : hdist u ((g ^ m) • u)
        = hdist (h • (h⁻¹ • u)) ((g ^ m) • (h • (h⁻¹ • u))) := by rw [hw]
    calc hdist u ((g ^ m) • u)
        = hdist (h • (h⁻¹ • u)) ((g ^ m) • (h • (h⁻¹ • u))) := hstep1
      _ = hdist (h • (h⁻¹ • u)) (h • ((h⁻¹ * g ^ m * h) • (h⁻¹ • u))) := by rw [hgm]
      _ = hdist (h⁻¹ • u) ((h⁻¹ * g ^ m * h) • (h⁻¹ • u)) := hId.isom_smul h _ _
      _ = hdist (h⁻¹ • u) ((A : PO n 1) • (h⁻¹ • u)) := by rw [hAcoe]
  rw [hkey]; exact h2

/-! ### A frequently bounded displacement along the ray fixes the boundary point -/

/-- From a frequently-attained property along `atTop` extract a strictly increasing sequence
of indices where it holds. -/
theorem exists_subseq_of_frequently {p : ℕ → Prop} (h : ∃ᶠ k : ℕ in atTop, p k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, p (φ k) := by
  have hf : ∀ a : ℕ, ∃ b : ℕ, a ≤ b ∧ p b := fun a => (Filter.frequently_atTop.mp h) a
  let φ : ℕ → ℕ := Nat.rec (Classical.choose (hf 0)) (fun _ pm => Classical.choose (hf (pm + 1)))
  have h0 : p (φ 0) := (Classical.choose_spec (hf 0)).2
  have hs : ∀ m, φ m + 1 ≤ φ (m + 1) ∧ p (φ (m + 1)) :=
    fun m => Classical.choose_spec (hf (φ m + 1))
  have hmono : StrictMono φ := strictMono_nat_of_lt_succ fun m => Nat.lt_of_succ_le (hs m).1
  refine ⟨φ, hmono, ?_⟩
  intro k
  induction k with
  | zero => exact h0
  | succ m _ => exact (hs m).2

/-- If `g` moves the points of the ray to `ζ` by at most `C` infinitely often, then `g` fixes `ζ`
on the boundary. -/
theorem bd_eq_of_frequently_close_rayN (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ζ : E n) (hζ : ζ ∈ Sph n) (g : PO n 1) (C : ℝ)
    (h : ∃ᶠ k : ℕ in atTop, hdist (rayN ζ k) (g • rayN ζ k) ≤ C) : bd g ζ = ζ := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨φ, hmono, hP⟩ := exists_subseq_of_frequently h
  have hφtop : Tendsto φ atTop atTop := hmono.tendsto_atTop
  set u : ℕ → E n := fun k => rayN ζ (φ k) with hu
  set v : ℕ → E n := fun k => g • rayN ζ (φ k) with hv
  have hlvl_u : Tendsto (fun k => BdExt.lvl (u k)) atTop atTop := by
    have hEq : (fun k => BdExt.lvl (u k)) = fun k : ℕ => (((φ k : ℕ)) : ℝ) := by
      funext k
      rw [hu]
      show BdExt.lvl (BdExt.ray ζ (((φ k : ℕ)) : ℝ)) = _
      rw [BdExt.lvl, BdExt.hdist_zero_ray ζ hζ _ (Nat.cast_nonneg _)]
    rw [hEq]
    exact tendsto_natCast_atTop_atTop.comp hφtop
  have hlvl_v : Tendsto (fun k => BdExt.lvl (v k)) atTop atTop := by
    refine tendsto_atTop_mono (f := fun k => BdExt.lvl (u k) + (-C)) (fun k => ?_) ?_
    · have h4 : BdExt.lvl (u k) ≤ BdExt.lvl (v k) + hdist (v k) (u k) := by
        have h5 := hId.triangle (0 : E n) (v k) (u k)
        simpa [BdExt.lvl] using h5
      have h6 : hdist (v k) (u k) = hdist (u k) (v k) := hId.symm _ _
      have h3 : hdist (u k) (v k) ≤ C := by rw [hu, hv]; exact hP k
      linarith
    · simpa using Filter.tendsto_atTop_add_const_right atTop (-C) hlvl_u
  have hdir_u : Tendsto (fun k => BdExt.dirv (u k)) atTop (nhds ζ) := by
    have h1 := (BdExt.tendsto_dirv_ray hI ζ hζ).comp hφtop
    have hEq : (fun k => BdExt.dirv (u k)) =
        fun k => BdExt.dirv (BdExt.ray ζ (((φ k : ℕ)) : ℝ)) := by
      funext k; rw [hu]; rfl
    rw [hEq]; exact h1
  have hCnn : 0 ≤ C := le_trans (hId.nonneg _ _) (hP 0)
  have hdir_v : Tendsto (fun k => BdExt.dirv (v k)) atTop (nhds ζ) := by
    have h1 := BdExt.closeSeq n hI u v C hCnn (fun k => by rw [hu, hv]; exact hP k) hlvl_u hlvl_v ζ hdir_u
    exact h1
  have hnorm_u : Tendsto (fun k : ℕ => ‖u k‖) atTop atTop := by
    have hEq : (fun k : ℕ => ‖u k‖) = fun k : ℕ => Real.sinh (((φ k : ℕ)) : ℝ) := by
      funext k
      rw [hu]
      show ‖BdExt.ray ζ (((φ k : ℕ)) : ℝ)‖ = _
      rw [BdExt.norm_eq_sinh_lvl, BdExt.lvl, BdExt.hdist_zero_ray ζ hζ _ (Nat.cast_nonneg _)]
    rw [hEq]
    exact BdExt.tendsto_sinh_atTop'.comp (tendsto_natCast_atTop_atTop.comp hφtop)
  have hdir_conv : Tendsto (fun k => BdExt.dirv (v k)) atTop (nhds (bd g ζ)) := by
    have h1 := BdExt.isomConv n hA hI g u ζ hζ hnorm_u hdir_u
    have hEq : (fun k => BdExt.dirv (g • u k)) = fun k => BdExt.dirv (v k) := by
      funext k; rw [hv]
    rw [hEq] at h1
    exact h1
  exact tendsto_nhds_unique hdir_conv hdir_v


/-! ### The main theorem -/

theorem HL_of_escapeShort (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hM : MargulisCuspProp n) (hL : MargulisLoxProp n) (hPS : PairStabProp n) (hC : ClassifyProp n)
    (hPF : ∀ g : PO n 1, IsParabolic g → (∃ ξ : E n, ξ ∈ Sph n ∧ bd g ξ = ξ) ∧
      ∀ ξ η : E n, ξ ∈ Sph n → η ∈ Sph n → bd g ξ = ξ → bd g η = η → ξ = η)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (hstab : ∀ ξ : E n, ξ ∈ Sph n → (∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ξ = ξ) →
      ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → busemann ξ ((γ : PO n 1) • (0 : E n)) = 0)
    (hesc : ∀ ε : ℝ, 0 < ε → ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
      (∀ γ : Γ, (γ : PO n 1) • u ∉ K) → ∃ g : Γ, orderOf g = 0 ∧ hdist u ((g : PO n 1) • u) < ε)
    (ζ : E n) (hζ : ζ ∈ Sph n) (s : ℝ)
    (hfree : ∀ γ : Γ, (γ : PO n 1) • (0 : E n) ∉ horoball ζ s)
    (hβζ : ∀ γ : Γ, bd (γ : PO n 1) ζ = ζ → busemann ζ ((γ : PO n 1) • (0 : E n)) = 0)
    : ∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ζ = ζ := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the two Margulis constants
  obtain ⟨εM, hεMpos, hεM⟩ := hM 3
  obtain ⟨ηL, hηLpos, hηL⟩ := hL 3
  set η : ℝ := min (min εM ηL) 1 with hηdef
  have hηpos : 0 < η := lt_min (lt_min hεMpos hηLpos) one_pos
  have hηεM : η ≤ εM := le_trans (min_le_left _ _) (min_le_left _ _)
  have hηηL : η ≤ ηL := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη1 : η ≤ 1 := min_le_right _ _
  -- near-identity powers, and the smallness constant for the escape
  obtain ⟨M, ε₁, hMpos, hε₁pos, hpw⟩ := nearIdAt_of_short n hA hI η hηpos
  set ε : ℝ := min ε₁ (η / M) with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos (div_pos hηpos (Nat.cast_pos.mpr hMpos))
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hεMle : ε * (M : ℝ) ≤ η := by
    have h1 : ε ≤ η / M := min_le_right _ _
    have h2 : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
    calc ε * (M : ℝ) ≤ (η / M) * (M : ℝ) := by nlinarith [h1]
      _ = η := by field_simp
  -- the escape set
  obtain ⟨K, hK, hKesc⟩ := hesc ε hεpos
  obtain ⟨T₁, hT₁⟩ := escape_of_horoball n hA hI Γ ζ hζ s hfree K hK
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T₁ ≤ (T : ℝ) := exists_nat_ge T₁
  -- at every ray point beyond `T` there is an infinite-order near-identity element
  have hstep : ∀ k : ℕ, ∃ γ : Γ, orderOf γ = 0 ∧ NearIdAt (γ : PO n 1) (rayN ζ (T + k)) η ∧
      hdist (rayN ζ (T + k)) ((γ : PO n 1) • rayN ζ (T + k)) < η := by
    intro k
    have hTk : T₁ ≤ (((T + k : ℕ)) : ℝ) := by
      have h2 : (T : ℝ) ≤ (((T + k : ℕ)) : ℝ) := by
        push_cast
        exact_mod_cast Nat.le_add_right T k
      linarith
    have hnotmem : ∀ γ : Γ, (γ : PO n 1) • rayN ζ (T + k) ∉ K := by
      intro γ
      have h2 := hT₁ (((T + k : ℕ)) : ℝ) hTk γ
      simpa [rayN, BdExt.ray] using h2
    obtain ⟨g, hgord, hgshort⟩ := hKesc (rayN ζ (T + k)) hnotmem
    obtain ⟨m, hm1, hmM, hnear⟩ := hpw (rayN ζ (T + k)) (g : PO n 1) (lt_of_lt_of_le hgshort hεε₁)
    refine ⟨g ^ m, orderOf_pow_eq_zero g hm1 hgord, hnear, ?_⟩
    have hzz : hdist (rayN ζ (T + k)) (rayN ζ (T + k)) ≤ 1 := by
      rw [hdist_rayN_self ζ hζ]; norm_num
    exact hnear _ hzz
  choose γseq hγseq_ord hγseq_near hγseq_short using hstep
  have hnofix : ∀ k, ∀ p : E n, ((γseq k : Γ) : PO n 1) • p ≠ p := fun k =>
    no_fixed_of_orderOf_zero n hA hI Γ hdisc (γseq k) (hγseq_ord k)
  -- the distance of `γseq (j+1)` to the ray point `rayN ζ (T+j)`
  have hhcl : ∀ j : ℕ, hdist (rayN ζ (T + j)) (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j)) ≤ 3 := by
    intro j
    have hmid : hdist (rayN ζ (T + j + 1))
        (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j + 1)) ≤ 1 := by
      have h1 := hγseq_short (j+1)
      have h2 : rayN ζ (T + (j+1)) = rayN ζ (T + j + 1) := by rw [Nat.add_assoc]
      rw [h2] at h1
      exact le_of_lt (lt_of_lt_of_le h1 hη1)
    have h3 : hdist (rayN ζ (T + j)) (rayN ζ (T + j + 1)) ≤ 1 := by
      rw [hdist_rayN ζ hζ]
      have h4 : (((T + j : ℕ)) : ℝ) - (((T + j + 1 : ℕ)) : ℝ) = -1 := by push_cast; ring
      rw [h4, abs_neg, abs_one]
    have h5 : hdist (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j + 1))
        (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j)) ≤ 1 := by
      rw [hId.isom_smul, hId.symm]
      exact h3
    calc hdist (rayN ζ (T + j)) (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j))
        ≤ hdist (rayN ζ (T + j)) (rayN ζ (T + j + 1))
          + hdist (rayN ζ (T + j + 1)) (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j + 1))
          + hdist (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j + 1))
              (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j)) := by
          have h6 := hId.triangle (rayN ζ (T + j)) (rayN ζ (T + j + 1))
            (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j + 1))
          have h7 := hId.triangle (rayN ζ (T + j))
            (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j + 1))
            (((γseq (j+1) : Γ) : PO n 1) • rayN ζ (T + j))
          linarith
      _ ≤ 3 := by linarith
  rcases hC ((γseq 0 : Γ) : PO n 1) (hnofix 0) with hpar0 | ⟨x, y, hlox0⟩
  · -- ## the parabolic branch
    obtain ⟨ξ, hξ, hγ0ξ⟩ := (hPF ((γseq 0 : Γ) : PO n 1) hpar0).1
    have hinduct : ∀ k, IsParabolic (((γseq k : Γ) : PO n 1)) ∧
        bd (((γseq k : Γ) : PO n 1)) ξ = ξ := by
      intro k
      induction k with
      | zero => exact ⟨hpar0, hγ0ξ⟩
      | succ j ih =>
        have hlink : bd (((γseq (j+1) : Γ) : PO n 1)) ξ = ξ :=
          hεM Γ hdisc (rayN ζ (T + j)) ξ (γseq j) (γseq (j+1))
            ih.1 hξ ih.2 (lt_of_lt_of_le (hγseq_short j) hηεM) (hhcl j)
        have hnof := hnofix (j+1)
        rcases hC (((γseq (j+1) : Γ) : PO n 1)) hnof with hpar | ⟨a, b, hlox⟩
        · exact ⟨hpar, hlink⟩
        · exfalso
          have hβ : busemann ξ (((γseq (j+1) : Γ) : PO n 1) • (0 : E n)) = 0 :=
            hstab ξ hξ ⟨γseq j, ih.1, ih.2⟩ (γseq (j+1)) hlink
          have hfix2 : ∃ ξ' : E n, ξ' ∈ Sph n ∧ ξ ≠ ξ' ∧
              bd (((γseq (j+1) : Γ) : PO n 1)) ξ' = ξ' := by
            by_cases h1 : ξ = a
            · refine ⟨b, hlox.2.1, ?_, hlox.2.2.2.2.1⟩
              rw [h1]; exact hlox.2.2.1
            · exact ⟨a, hlox.1, h1, hlox.2.2.2.1⟩
          obtain ⟨ξ', hξ', hne', hfix'⟩ := hfix2
          obtain ⟨p, hp⟩ := exists_fixed_of_two_bd_fixes hI hPS hξ hξ' hne' hlink hfix' hβ
          exact hnof p hp
    by_cases hξζ : ξ = ζ
    · exact ⟨γseq 0, (hinduct 0).1, by rw [← hξζ]; exact (hinduct 0).2⟩
    · exfalso
      have hfixall : ∀ k, bd (((γseq k : Γ) : PO n 1)) ξ = ξ := fun k => (hinduct k).2
      have hβall : ∀ k, busemann ξ (((γseq k : Γ) : PO n 1) • (0 : E n)) = 0 := fun k =>
        hstab ξ hξ ⟨γseq 0, (hinduct 0).1, (hinduct 0).2⟩ (γseq k) (hfixall k)
      have hnearall : ∀ k, hdist (rayN ζ (T + k)) (((γseq k : Γ) : PO n 1) • rayN ζ (T + k)) ≤ 1 :=
        fun k => le_of_lt (lt_of_lt_of_le (hγseq_short k) hη1)
      obtain ⟨g, hgfreq⟩ := parabolic_pin hA hI hξ hζ hξζ Γ hdisc (fun k => T + k) γseq
        hfixall hβall hnearall
      have hfreq' : ∃ᶠ k : ℕ in atTop, hdist (rayN ζ k) (((g : Γ) : PO n 1) • rayN ζ k) ≤ 1 := by
        rw [Filter.frequently_atTop] at hgfreq ⊢
        intro a
        obtain ⟨k, hk, hgk⟩ := hgfreq a
        exact ⟨T + k, le_trans hk (Nat.le_add_left k T), by rw [← hgk]; exact hnearall k⟩
      have hbdζ : bd (((g : Γ) : PO n 1)) ζ = ζ :=
        bd_eq_of_frequently_close_rayN n hA hI ζ hζ ((g : Γ) : PO n 1) 1 hfreq'
      obtain ⟨k, hgk⟩ := hgfreq.exists
      have hpg : IsParabolic (((g : Γ) : PO n 1)) := by rw [← hgk]; exact (hinduct k).1
      have hfixg : bd (((g : Γ) : PO n 1)) ξ = ξ := by rw [← hgk]; exact (hinduct k).2
      exact hξζ ((hPF ((g : Γ) : PO n 1) hpg).2 ξ ζ hξ hζ hfixg hbdζ)
  · -- ## the loxodromic branch
    exfalso
    have hinduct : ∀ k, LoxPair (((γseq k : Γ) : PO n 1)) x y := by
      intro k
      induction k with
      | zero => exact hlox0
      | succ j ih =>
        have hpres := hηL Γ hdisc (rayN ζ (T + j)) x y (γseq j) (γseq (j+1))
          ih (NearIdAt_mono (hγseq_near j) hηηL) (hhcl j)
        have hfix := no_swap_of_preserves_pair hlox0.1 hlox0.2.1 hlox0.2.2.1 (hnofix (j+1)) hpres
        have hβ : busemann x (((γseq (j+1) : Γ) : PO n 1) • (0 : E n)) ≠ 0 := by
          intro h0
          obtain ⟨p, hp⟩ := exists_fixed_of_two_bd_fixes hI hPS hlox0.1 hlox0.2.1 hlox0.2.2.1
            hfix.1 hfix.2 h0
          exact hnofix (j+1) p hp
        exact ⟨hlox0.1, hlox0.2.1, hlox0.2.2.1, hfix.1, hfix.2, hβ⟩
    obtain ⟨p, hp⟩ := hPS x y hlox0.1 hlox0.2.1 hlox0.2.2.1
    have hbound : ∀ k, hdist p (((γseq k : Γ) : PO n 1) • p) ≤ η := by
      intro k
      have hk := hinduct k
      have h1 := (hp ((γseq k) : PO n 1) hk.2.2.2.1 hk.2.2.2.2.1).1
      have h2 : |busemann x (((γseq k : Γ) : PO n 1) • (0 : E n))| ≤
          hdist (rayN ζ (T + k)) (((γseq k : Γ) : PO n 1) • rayN ζ (T + k)) := by
        have hc := hId.busemann_cocycle (((γseq k : Γ) : PO n 1)) x (rayN ζ (T + k)) hlox0.1
        rw [hk.2.2.2.1] at hc
        have h3 := BusemannLipschitz n x hlox0.1 (rayN ζ (T + k))
          (((γseq k : Γ) : PO n 1) • rayN ζ (T + k))
        have hd : busemann x (rayN ζ (T + k))
            - busemann x (((γseq k : Γ) : PO n 1) • rayN ζ (T + k))
            = -busemann x (((γseq k : Γ) : PO n 1) • (0 : E n)) := by
          rw [hc]; ring
        calc |busemann x (((γseq k : Γ) : PO n 1) • (0 : E n))|
            = |busemann x (rayN ζ (T + k))
                - busemann x (((γseq k : Γ) : PO n 1) • rayN ζ (T + k))| := by
              rw [hd, abs_neg]
          _ ≤ hdist (rayN ζ (T + k)) (((γseq k : Γ) : PO n 1) • rayN ζ (T + k)) := h3
      rw [h1]
      exact le_trans h2 (le_of_lt (hγseq_short k))
    have hfin : {γ : Γ | hdist p (((γ : Γ) : PO n 1) • p) ≤ η}.Finite :=
      finite_hdist_orbit_ball hA hI hdisc p η
    obtain ⟨g, hgfreq⟩ := exists_frequently_fiber γseq 0 _ hfin (fun k _ => hbound k)
    have hfreq' : ∃ᶠ k : ℕ in atTop, hdist (rayN ζ k) (((g : Γ) : PO n 1) • rayN ζ k) ≤ η := by
      rw [Filter.frequently_atTop] at hgfreq ⊢
      intro a
      obtain ⟨k, hk, hgk⟩ := hgfreq a
      exact ⟨T + k, le_trans hk (Nat.le_add_left k T),
        by rw [← hgk]; exact le_of_lt (hγseq_short k)⟩
    have hbdζ : bd (((g : Γ) : PO n 1)) ζ = ζ :=
      bd_eq_of_frequently_close_rayN n hA hI ζ hζ ((g : Γ) : PO n 1) η hfreq'
    have hβζg : busemann ζ (((g : Γ) : PO n 1) • (0 : E n)) = 0 := hβζ g hbdζ
    obtain ⟨k, hgk⟩ := hgfreq.exists
    have hloxg : LoxPair (((g : Γ) : PO n 1)) x y := by rw [← hgk]; exact hinduct k
    have hgord : orderOf g = 0 := by rw [← hgk]; exact hγseq_ord k
    have hnofixg := no_fixed_of_orderOf_zero n hA hI Γ hdisc g hgord
    by_cases hζx : ζ = x
    · exact hloxg.2.2.2.2.2 (by rw [← hζx]; exact hβζg)
    · by_cases hζy : ζ = y
      · obtain ⟨p', hp'⟩ := exists_fixed_of_two_bd_fixes hI hPS hlox0.2.1 hlox0.1
          (fun h => hlox0.2.2.1 h.symm) hloxg.2.2.2.2.1 hloxg.2.2.2.1 (by rw [← hζy]; exact hβζg)
        exact hnofixg p' hp'
      · obtain ⟨p', hp'⟩ := exists_fixed_of_two_bd_fixes hI hPS hζ hlox0.1
          (fun h => hζx h) hbdζ hloxg.2.2.2.1 hβζg
        exact hnofixg p' hp'

end

end Work.Mostow

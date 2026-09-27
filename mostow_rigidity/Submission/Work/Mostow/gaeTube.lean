import Mathlib
import Submission.Work.Mostow.gapAEvenDefs
import Submission.Work.Mostow.ftbUnfold
import Submission.Work.Mostow.ftbConjCount
import Submission.Work.Mostow.ftbTubeQuot
import Submission.Work.Mostow.tubeMeasure_ball2
import Submission.Work.Mostow.tube_nearId
import Submission.Work.Mostow.resStdDiscreteStrata
import Submission.Work.Mostow.dirichletSet_isFundamentalDomain
import Submission.Work.Mostow.cardKernelTorus
import Submission.Work.Mostow.centralizer_acts_fermi
import Submission.Work.Mostow.cardKAux
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.hBallVolumeLower
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.gaeFD
import Submission.Work.Mostow.gapA_all_aux
import Submission.Work.Mostow.poAction_hypIso_zero

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-! ## Elementary action facts -/

private lemma p_smul_mul {n : ℕ} (hA : POActionProp n) (g h : PO n 1) (u : E n) :
    (g * h) • u = g • (h • u) := hA.2.2.2.2.1 g h u

private lemma p_smul_one {n : ℕ} (hA : POActionProp n) (u : E n) : (1 : PO n 1) • u = u :=
  hA.2.2.2.1 u

private lemma p_eq_of_smul_eq {n : ℕ} (hA : POActionProp n) {g g' : PO n 1}
    (h : ∀ u : E n, g • u = g' • u) : g = g' := by
  have h1 : g⁻¹ * g' = 1 := hA.2.2.2.2.2.1 (g⁻¹ * g') (fun u => by
    rw [p_smul_mul hA, ← h u, ← p_smul_mul hA, inv_mul_cancel, p_smul_one hA])
  exact inv_mul_eq_one.mp h1

private lemma p_subsingleton_PO_zero : Subsingleton (PO 0 1) :=
  ⟨fun g h => p_eq_of_smul_eq poAction_zero (fun u => Subsingleton.elim _ _)⟩

private lemma p_fermi_zero (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  simp [fermi, coordEmb, sinhc]

/-! ## The fixed set of a pure block is the standard stratum -/

private lemma p_fixSet_blk {j m : ℕ} (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w : E m, R w = w → w = 0) :
    fixSet (blk j m 1 R) = stdTG j m := by
  ext u
  constructor
  · intro hu
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi j m v w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
    change (blk j m 1 R) • fermi j m v w = fermi j m v w at hu
    rw [blk_smul_fermi j m hAj hIj hA hI 1 R v w, hAj.2.2.2.1 v] at hu
    have h3 := congrArg (fermiInv j m) hu
    rw [(fermi_inv j m).1 v (R w), (fermi_inv j m).1 v w] at h3
    have h2 : R w = w := (Prod.ext_iff.mp h3).2
    have hw : w = 0 := hR w h2
    subst hw
    exact ⟨v, (p_fermi_zero j m v).symm⟩
  · rintro ⟨v, rfl⟩
    change (blk j m 1 R) • coordEmb j m v = coordEmb j m v
    rw [← p_fermi_zero j m v, blk_smul_fermi j m hAj hIj hA hI 1 R v 0, hAj.2.2.2.1 v,
      R.map_zero]

/-! ## Centraliser elements preserve the standard stratum -/

private lemma p_centralizer_mem_SetStabStd {j m : ℕ} (hAj : POActionProp j)
    (hIj : HypIsometryProp j) (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w : E m, R w = w → w = 0) {c : PO (j + m) 1}
    (hc : c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1))) :
    c ∈ SetStabStd j m := by
  have hfix : fixSet (blk j m 1 R) = stdTG j m := p_fixSet_blk hAj hIj hA hI R hR
  have hcomm : (blk j m 1 R) * c = c * (blk j m 1 R) :=
    (Subgroup.mem_centralizer_iff.mp hc) (blk j m 1 R) (Set.mem_singleton _)
  intro u
  constructor
  · intro hu
    rw [← hfix] at hu ⊢
    show (blk j m 1 R) • (c • u) = c • u
    rw [← p_smul_mul hA, hcomm, p_smul_mul hA, hu]
  · intro hu
    rw [← hfix] at hu ⊢
    have h2 : c⁻¹ • ((blk j m 1 R) • (c • u)) = c⁻¹ • (c • u) := by rw [hu]
    have hL : c⁻¹ • ((blk j m 1 R) • (c • u)) = (c⁻¹ * (blk j m 1 R) * c) • u := by
      rw [← p_smul_mul hA c⁻¹ (blk j m 1 R) (c • u),
        ← p_smul_mul hA (c⁻¹ * (blk j m 1 R)) c u]
    have hR' : c⁻¹ • (c • u) = u := by
      rw [← p_smul_mul hA c⁻¹ c u, inv_mul_cancel, p_smul_one hA]
    have h3 : c⁻¹ * (blk j m 1 R) * c = blk j m 1 R := by
      rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h4 : (c⁻¹ * (blk j m 1 R) * c) • u = u := by rw [← hL, h2, hR']
    rwa [h3] at h4

/-! ## The volume of `E 0` and of fundamental domains in dimension `0` -/

private lemma p_volH_zero_univ : volH 0 (Set.univ : Set (E 0)) = 1 := by
  have hdens1 : (hdens : E 0 → ℝ≥0∞) = 1 := by
    funext u
    have ht : tpart u = 1 := by
      rw [tpart]
      have h0 : ‖u‖ = 0 := norm_eq_zero.mpr (Subsingleton.elim u 0)
      rw [h0]; norm_num
    rw [hdens_apply, ht]; norm_num
  rw [volH_def, hdens1, withDensity_one]
  exact volume_univ_fin_zero

private lemma p_volH_zero_fd {G : Subgroup (PO 0 1)} {D : Set (E 0)}
    (hD : IsFundamentalDomain ↥G D (volH 0)) : volH 0 D = 1 := by
  haveI : Subsingleton (PO 0 1) := p_subsingleton_PO_zero
  have hmem : ∀ᵐ x ∂(volH 0), x ∈ D := by
    refine hD.ae_covers.mono (fun x hx => ?_)
    obtain ⟨g, hg⟩ := hx
    have hg1 : g = 1 := Subsingleton.elim _ _
    rw [hg1] at hg
    have hx1 : (1 : ↥G) • x = x := p_smul_one poAction_zero x
    rwa [hx1] at hg
  have hfull : D =ᵐ[volH 0] Set.univ := by
    filter_upwards [hmem] with x hx
    simp [hx]
  rw [measure_congr hfull, p_volH_zero_univ]

private lemma p_covolLB_zero : CovolLB 0 := by
  refine ⟨1, one_pos, ?_⟩
  intro Λ hdisc D hD
  rw [p_volH_zero_fd hD, ENNReal.ofReal_one]

/-! ## The general unfolding bound at an arbitrary near-identity scale -/

private theorem p_ftbUnfoldGen (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (η₁ : ℝ) (hη₁ : 0 < η₁) :
    ∀ (Λ : Subgroup (PO (j + m) 1)) (D Dc : Set (E (j + m)))
      (b : PO (j + m) 1) (Cℓ : ℕ),
      IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (j + m)) → b ∈ Λ →
      IsFundamentalDomain ↥(Subgroup.centralizer ({b} : Set (PO (j + m) 1)) ⊓ Λ) Dc (volH (j + m)) →
      (∀ w : E (j + m), NearIdAt b w η₁ →
        {c : PO (j + m) 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ}.ncard ≤ Cℓ) →
      volH (j + m) ({u : E (j + m) | NearIdAt b u η₁} ∩ Dc)
        ≤ (Cℓ : ENNReal) * volH (j + m) D := by
  intro Λ D Dc b Cℓ hdisc hD hb hDc hCℓ
  set Es : Set (E (j + m)) := toMeasurable (volH (j + m)) Dc with hEs
  have hEmeas : MeasurableSet Es := by rw [hEs]; exact measurableSet_toMeasurable _ _
  have hEae : Es =ᵐ[volH (j + m)] Dc := by
    rw [hEs]; exact hDc.nullMeasurableSet.toMeasurable_ae_eq
  have hBadNull := ftb_badSetNull hA hI Λ hdisc b Dc hDc
  have hBadNull' : volH (j + m) {z : E (j + m) | ∃ (γ : Λ)
      (c : ↥(Subgroup.centralizer ({b} : Set (PO (j + m) 1)) ⊓ Λ)),
        c ≠ 1 ∧ (γ : PO (j + m) 1) • z ∈ Es ∧
          (c : PO (j + m) 1) • ((γ : PO (j + m) 1) • z) ∈ Es} = 0 := by
    rw [hEs]; exact hBadNull
  have hcount : ∀ᵐ z ∂((volH (j + m)).restrict D), ∃ s : Finset Λ, s.card ≤ Cℓ ∧
      ∀ γ : Λ, (γ : PO (j + m) 1) • z ∈ {u : E (j + m) | NearIdAt b u η₁} ∩ Es → γ ∈ s := by
    rw [ae_restrict_iff'₀ hD.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBadNull'] with z hz hzD
    refine ftb_countAtGood hA hI Λ hdisc b hb η₁ Cℓ hCℓ
      {u : E (j + m) | NearIdAt b u η₁} (fun u hu => hu) Es z ?_
    intro γ c hcne hγEs hcontra
    exact hz ⟨γ, c, hcne, hγEs, hcontra⟩
  have hFmeas : MeasurableSet ({u : E (j + m) | NearIdAt b u η₁} ∩ Es) :=
    (ftbMeasurableSetNearId (j + m) hA hI b η₁).inter hEmeas
  have hvol_eq : volH (j + m) ({u : E (j + m) | NearIdAt b u η₁} ∩ Dc)
      = volH (j + m) ({u : E (j + m) | NearIdAt b u η₁} ∩ Es) :=
    measure_congr (ae_eq_set_inter (ae_eq_refl _) hEae.symm)
  have hmain := volH_le_card_mul_of_ae_count (j + m) hA hI Λ hdisc (D := D)
    (F := {u : E (j + m) | NearIdAt b u η₁} ∩ Es) hD hFmeas Cℓ hcount
  rw [hvol_eq]
  exact hmain

/-! ## The cardinality bound for subgroups of `O(m)` with a separation scale -/

private lemma p_orthCard (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite A] (v : ℝ), 0 < v → v ≤ 1 →
      (∀ a ∈ A, a ≠ 1 → v ≤ rotN a) →
      (Nat.card A : ℝ) ≤ C * v ^ (-(m : ℝ) / 2) := by
  obtain ⟨J₀, hJ₀pos, hJ₀⟩ := exists_abelian_subgroup_index m
  obtain ⟨K₀, hK₀pos, hK₀⟩ := abelianCardBound m
  refine ⟨J₀ * (2 * K₀), by positivity, ?_⟩
  intro A hAfin v hv hv1 hsep
  obtain ⟨B, hBcomm, hBcard⟩ := hJ₀ A
  set B' : Subgroup (E m ≃ₗᵢ[ℝ] E m) := B.map (Subgroup.subtype A) with hB'def
  haveI : Finite ↥B' := by
    refine Finite.of_surjective (fun b : ↥B => (⟨(b : ↥A), ?_⟩ : ↥B')) ?_
    · rw [hB'def]; exact ⟨b, b.2, rfl⟩
    · rintro ⟨a, ha⟩
      rw [hB'def] at ha
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
      exact ⟨⟨b, hb⟩, Subtype.ext hba⟩
  have hB'comm : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    rw [hB'def] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg (fun x : ↥A => (x : E m ≃ₗᵢ[ℝ] E m)) (hBcomm a₀ ha₀ b₀ hb₀)
  have hB'sep : ∀ a ∈ B', a ≠ 1 → v ≤ rotN a := by
    intro a ha ha1
    rw [hB'def] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    exact hsep a₀ (Subtype.coe_prop a₀) ha1
  have hcard_le : Nat.card ↥B ≤ Nat.card ↥B' :=
    Nat.card_le_card_of_injective (fun b : ↥B => (⟨(b : ↥A), by
      rw [hB'def]; exact ⟨b, b.2, rfl⟩⟩ : ↥B')) (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥B' => (z : E m ≃ₗᵢ[ℝ] E m)) hxy)))
  have hBbound : (Nat.card ↥B : ℝ) ≤ K₀ * (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ)) := by
    have h1 := hK₀ B' v hv hB'comm hB'sep
    have h2 : (Nat.card ↥B : ℝ) ≤ (Nat.card ↥B' : ℝ) := by exact_mod_cast hcard_le
    linarith
  have h3 : (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ)) ≤ 2 * (v : ℝ) ^ (-(m : ℝ) / 2) := by
    have hX1 : (1:ℝ) ≤ (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ) := by
      rw [zpow_neg, zpow_natCast]
      exact (one_le_inv₀ (pow_pos hv _)).mpr (pow_le_one₀ (le_of_lt hv) hv1)
    have hXY : (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ) ≤ (v : ℝ) ^ (-(m : ℝ) / 2) := by
      rw [show (-(m : ℝ) / 2) = -((m : ℝ) / 2) by ring]
      have hz : (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ) = ((v : ℝ) ^ (m / 2 : ℕ))⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      have hr : (v : ℝ) ^ (-((m : ℝ) / 2)) = ((v : ℝ) ^ ((m : ℝ) / 2))⁻¹ :=
        Real.rpow_neg (le_of_lt hv) _
      rw [hz, hr]
      refine (inv_le_inv₀ (pow_pos hv _) (Real.rpow_pos_of_pos hv _)).mpr ?_
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hv hv1 (by
        have h2 : ((m / 2 : ℕ) : ℝ) * 2 ≤ (m : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self m 2
        linarith)
    linarith
  calc (Nat.card ↥A : ℝ) ≤ J₀ * (Nat.card ↥B : ℝ) := hBcard
    _ ≤ J₀ * (K₀ * (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ))) :=
        mul_le_mul_of_nonneg_left hBbound (le_of_lt hJ₀pos)
    _ ≤ J₀ * (K₀ * (2 * (v : ℝ) ^ (-(m : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (le_of_lt hK₀pos))
          (le_of_lt hJ₀pos)
    _ = J₀ * (2 * K₀) * (v : ℝ) ^ (-(m : ℝ) / 2) := by ring

/-! ## The cardinality of the stratum kernel from the separation hypothesis -/

private lemma p_cardK (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : Subgroup (PO (j + m) 1)) (R : E m ≃ₗᵢ[ℝ] E m) (v : ℝ),
      IsDiscrete (SetLike.coe Λ) → blk j m 1 R ∈ Λ → (∀ w : E m, R w = w → w = 0) →
      0 < v → v ≤ 1 →
      (∀ c : PO (j + m) 1, c ∈ Λ →
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
        resStd j m c = 1 → c ≠ 1 → v ≤ rotN (nrmStd j m c)) →
      (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
        resStd j m c = 1} : ENNReal) ≤ ENNReal.ofReal (C * v ^ (-(m : ℝ) / 2)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := p_orthCard m
  refine ⟨C₀, hC₀pos, ?_⟩
  intro Λ R v hdisc hb hfree hv0 hv1 hsep
  have hblock : ∀ c : PO (j + m) 1, c ∈ Λ →
      c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
      resStd j m c = 1 → c = blk j m 1 (nrmStd j m c) := by
    intro c hcΛ hcC hcS
    have h1 : c = blk j m (resStd j m c) (nrmStd j m c) := by
      apply p_eq_of_smul_eq hA
      intro u
      obtain ⟨p, w, rfl⟩ : ∃ p w, u = fermi j m p w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
      rw [centralizer_acts_fermi j m hAj hIj hA hI R hfree c hcC p w,
        blk_smul_fermi j m hAj hIj hA hI (resStd j m c) (nrmStd j m c) p w]
    conv_lhs => rw [h1]
    rw [hcS]
  by_cases hfin : Finite {c : PO (j + m) 1 // c ∈ Λ ∧
      c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧ resStd j m c = 1}
  · haveI := hfin
    let A : Subgroup (E m ≃ₗᵢ[ℝ] E m) :=
      { carrier := {R' | blk j m 1 R' ∈ Λ ∧
            blk j m 1 R' ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
            resStd j m (blk j m 1 R') = 1},
        mul_mem' := by
          intro R' R'' hR' hR''
          have heq : blk j m 1 (R' * R'') = blk j m 1 R' * blk j m 1 R'' := by
            simpa using (blk_hom j m hAj hIj hA hI).1 1 1 R' R''
          change R' * R'' ∈ ({R' : E m ≃ₗᵢ[ℝ] E m |
              blk j m 1 R' ∈ Λ ∧ blk j m 1 R' ∈
                Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
              resStd j m (blk j m 1 R') = 1} : Set (E m ≃ₗᵢ[ℝ] E m))
          rw [Set.mem_setOf_eq, heq]
          exact ⟨Λ.mul_mem hR'.1 hR''.1,
            (Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1))).mul_mem hR'.2.1 hR''.2.1,
            by rw [← heq, resStd_blk j m hAj hIj hA hI]⟩
        one_mem' := by
          have h1 : blk j m 1 (1 : E m ≃ₗᵢ[ℝ] E m) = 1 :=
            (blk_hom j m hAj hIj hA hI).2.1
          change (1 : E m ≃ₗᵢ[ℝ] E m) ∈ ({R' : E m ≃ₗᵢ[ℝ] E m |
              blk j m 1 R' ∈ Λ ∧ blk j m 1 R' ∈
                Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
              resStd j m (blk j m 1 R') = 1} : Set (E m ≃ₗᵢ[ℝ] E m))
          rw [Set.mem_setOf_eq]
          refine ⟨?_, ?_, ?_⟩
          · rw [h1]; exact one_mem Λ
          · rw [h1]; exact one_mem _
          · rw [h1, resStd_one j m hAj hIj hA hI]
        inv_mem' := by
          intro R' hR'
          have h1 : blk j m 1 R' * blk j m 1 R'⁻¹ = 1 := by
            rw [← (blk_hom j m hAj hIj hA hI).1 1 1 R' R'⁻¹, mul_inv_cancel, one_mul,
              (blk_hom j m hAj hIj hA hI).2.1]
          have heq : blk j m 1 R'⁻¹ = (blk j m 1 R')⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
          change R'⁻¹ ∈ ({R' : E m ≃ₗᵢ[ℝ] E m |
              blk j m 1 R' ∈ Λ ∧ blk j m 1 R' ∈
                Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
              resStd j m (blk j m 1 R') = 1} : Set (E m ≃ₗᵢ[ℝ] E m))
          rw [Set.mem_setOf_eq, heq]
          exact ⟨Λ.inv_mem hR'.1,
            (Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1))).inv_mem hR'.2.1,
            by rw [← heq, resStd_blk j m hAj hIj hA hI]⟩ }
    have hsurj : Function.Surjective
        (fun c : {c : PO (j + m) 1 // c ∈ Λ ∧
            c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧ resStd j m c = 1} =>
          (⟨nrmStd j m (c : PO (j + m) 1), by
              change nrmStd j m (c : PO (j + m) 1) ∈ ({R' : E m ≃ₗᵢ[ℝ] E m |
                blk j m 1 R' ∈ Λ ∧ blk j m 1 R' ∈
                  Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
                resStd j m (blk j m 1 R') = 1} : Set (E m ≃ₗᵢ[ℝ] E m))
              rw [Set.mem_setOf_eq, ← hblock (c : PO (j + m) 1) c.2.1 c.2.2.1 c.2.2.2]
              exact c.2⟩ : ↥A)) := by
      rintro ⟨R', hR'⟩
      exact ⟨⟨blk j m 1 R', hR'⟩, Subtype.ext (nrmStd_blk j m hAj hIj hA hI 1 R')⟩
    haveI : Finite ↥A := Finite.of_surjective _ hsurj
    have hinj : Function.Injective
        (fun c : {c : PO (j + m) 1 // c ∈ Λ ∧
            c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧ resStd j m c = 1} =>
          (⟨nrmStd j m (c : PO (j + m) 1), by
              change nrmStd j m (c : PO (j + m) 1) ∈ ({R' : E m ≃ₗᵢ[ℝ] E m |
                blk j m 1 R' ∈ Λ ∧ blk j m 1 R' ∈
                  Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
                resStd j m (blk j m 1 R') = 1} : Set (E m ≃ₗᵢ[ℝ] E m))
              rw [Set.mem_setOf_eq, ← hblock (c : PO (j + m) 1) c.2.1 c.2.2.1 c.2.2.2]
              exact c.2⟩ : ↥A)) := by
      intro c d hcd
      have hcd' : nrmStd j m (c : PO (j + m) 1) = nrmStd j m (d : PO (j + m) 1) :=
        congrArg Subtype.val hcd
      refine Subtype.ext ?_
      rw [hblock (c : PO (j + m) 1) c.2.1 c.2.2.1 c.2.2.2,
        hblock (d : PO (j + m) 1) d.2.1 d.2.2.1 d.2.2.2, hcd']
    have hcard : (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
        resStd j m c = 1} : ℝ) ≤ (Nat.card ↥A : ℝ) := by
      exact_mod_cast Nat.card_le_card_of_injective _ hinj
    have hsepA : ∀ a ∈ A, a ≠ 1 → v ≤ rotN a := by
      intro a ha ha1
      have hmem : blk j m 1 (a : E m ≃ₗᵢ[ℝ] E m) ∈ Λ ∧
          blk j m 1 (a : E m ≃ₗᵢ[ℝ] E m) ∈
            Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
          resStd j m (blk j m 1 (a : E m ≃ₗᵢ[ℝ] E m)) = 1 := ha
      have hne : blk j m 1 (a : E m ≃ₗᵢ[ℝ] E m) ≠ 1 := by
        intro h
        apply ha1
        have h2 := (blk_hom j m hAj hIj hA hI).2.2 1 1 (a : E m ≃ₗᵢ[ℝ] E m) 1
          (by rw [h, (blk_hom j m hAj hIj hA hI).2.1])
        exact h2.2
      have := hsep (blk j m 1 (a : E m ≃ₗᵢ[ℝ] E m)) hmem.1 hmem.2.1 hmem.2.2 hne
      rwa [nrmStd_blk j m hAj hIj hA hI 1 (a : E m ≃ₗᵢ[ℝ] E m)] at this
    have hbound := hC₀ A v hv0 hv1 hsepA
    have hreal : (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
        resStd j m c = 1} : ℝ) ≤ C₀ * v ^ (-(m : ℝ) / 2) := le_trans hcard hbound
    rw [show (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
        resStd j m c = 1} : ENNReal) = ENNReal.ofReal ((Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
        resStd j m c = 1} : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hinf : Infinite {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧ resStd j m c = 1} :=
      not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero.mpr (Or.inr hinf)]
    simp



/-! ## The numerical core of the tube estimate -/

private lemma p_key (j m : ℕ) (cj c1 CcntR CcardR ηc K η θ ρ : ℝ)
    (hcj : 0 < cj) (hc1 : 0 < c1) (hCc : 0 < CcntR) (hCd : 0 < CcardR)
    (hηc : 0 < ηc) (hK : 0 < K) (hη : 0 < η) (hη1 : η ≤ 1) (hθ : 0 < θ) (hθη : θ ≤ K * η)
    (hjm1 : 1 ≤ j + m) (hs : 1 ≤ (j : ℝ) + (m : ℝ) / 2 - 1)
    (hρ : ηc / (2 * Real.exp 1 * θ) ≤ Real.exp ρ) :
    (cj * c1 * (ηc / (2 * Real.exp 1)) ^ (j + m - 1) / (CcardR * CcntR)
        * K ^ (-(((j + m - 1 : ℕ) : ℝ))))
      * η ^ (-(1 : ℝ)) * (CcardR * (θ / K) ^ (-(m : ℝ) / 2) * CcntR)
      ≤ cj * c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) := by
  have hN1c : ((j + m - 1 : ℕ) : ℝ) = (j : ℝ) + (m : ℝ) - 1 := by
    rw [Nat.cast_sub hjm1]; push_cast; ring
  have hθinv : ηc / (2 * Real.exp 1) * θ⁻¹ ≤ Real.exp ρ := by
    have h : ηc / (2 * Real.exp 1 * θ) = ηc / (2 * Real.exp 1) * θ⁻¹ := by
      field_simp
    rwa [h] at hρ
  have hA : (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * θ ^ (-(((j + m - 1 : ℕ) : ℝ)))
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) := by
    rw [Real.exp_nat_mul]
    have h1 : ((ηc / (2 * Real.exp 1)) * θ⁻¹) ^ (j + m - 1) ≤ (Real.exp ρ) ^ (j + m - 1) :=
      pow_le_pow_left₀ (by positivity) hθinv _
    have h2 : ((ηc / (2 * Real.exp 1)) * θ⁻¹) ^ (j + m - 1)
        = (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * θ ^ (-(((j + m - 1 : ℕ) : ℝ))) := by
      rw [mul_pow, inv_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_neg (le_of_lt hθ)]
    rwa [h2] at h1
  have hE : ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) ≤ -1 := by
    rw [hN1c]; linarith
  have hEpos : 0 ≤ -((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) := by linarith [hE]
  have hC : θ ^ (-(((j + m - 1 : ℕ) : ℝ))) * θ ^ ((m : ℝ) / 2)
      = θ ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) := by
    rw [← Real.rpow_add hθ]; ring_nf
  have hB : (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * θ ^ (-(((j + m - 1 : ℕ) : ℝ)))
        * θ ^ ((m : ℝ) / 2)
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * θ ^ ((m : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (le_of_lt hθ) _)
  have hB2 : (ηc / (2 * Real.exp 1)) ^ (j + m - 1)
        * (θ ^ (-(((j + m - 1 : ℕ) : ℝ))) * θ ^ ((m : ℝ) / 2))
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * θ ^ ((m : ℝ) / 2) := by
    rw [← mul_assoc]; exact hB
  rw [hC] at hB2
  have e1 : (K * η) ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
      = (((K * η) ^ (-((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))))⁻¹) := by
    simpa using Real.rpow_neg (le_of_lt (mul_pos hK hη))
      (-((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))))
  have e2 : θ ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
      = ((θ ^ (-((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))))⁻¹) := by
    simpa using Real.rpow_neg (le_of_lt hθ) (-((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))))
  have hD : (K * η) ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
      ≤ θ ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) := by
    rw [e1, e2]
    refine (inv_le_inv₀ (Real.rpow_pos_of_pos (mul_pos hK hη) _)
      (Real.rpow_pos_of_pos hθ _)).mpr ?_
    exact Real.rpow_le_rpow (le_of_lt hθ) hθη hEpos
  have hD2 : (ηc / (2 * Real.exp 1)) ^ (j + m - 1)
        * (K * η) ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * θ ^ ((m : ℝ) / 2) :=
    le_trans (mul_le_mul_of_nonneg_left hD (by positivity)) hB2
  rw [Real.mul_rpow (le_of_lt hK) (le_of_lt hη)] at hD2
  have hKc : K ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) * K ^ (-((m : ℝ) / 2))
      = K ^ (-(((j + m - 1 : ℕ) : ℝ))) := by
    rw [← Real.rpow_add hK]; ring_nf
  have hVc : θ ^ ((m : ℝ) / 2) * K ^ (-((m : ℝ) / 2)) = (θ / K) ^ ((m : ℝ) / 2) := by
    rw [show (θ / K) = θ * K⁻¹ by ring,
      Real.mul_rpow (le_of_lt hθ) (inv_nonneg.mpr (le_of_lt hK)),
      Real.inv_rpow (le_of_lt hK) ((m : ℝ) / 2),
      ← Real.rpow_neg (le_of_lt hK) ((m : ℝ) / 2)]
  have hfin : (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * K ^ (-(((j + m - 1 : ℕ) : ℝ)))
        * η ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * (θ / K) ^ ((m : ℝ) / 2) := by
    have h4 : ((ηc / (2 * Real.exp 1)) ^ (j + m - 1)
          * (K ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
            * η ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))))) * K ^ (-((m : ℝ) / 2))
        ≤ (Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * θ ^ ((m : ℝ) / 2))
            * K ^ (-((m : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hD2 (Real.rpow_nonneg (le_of_lt hK) _)
    have h5 : ((ηc / (2 * Real.exp 1)) ^ (j + m - 1)
          * (K ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
            * η ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))))) * K ^ (-((m : ℝ) / 2))
        = (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * K ^ (-(((j + m - 1 : ℕ) : ℝ)))
          * η ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) := by
      rw [← hKc]; ring
    have h6 : (Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * θ ^ ((m : ℝ) / 2))
          * K ^ (-((m : ℝ) / 2))
        = Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * (θ / K) ^ ((m : ℝ) / 2) := by
      rw [← hVc]; ring
    rwa [h5, h6] at h4
  have e3 : η ^ (-(1 : ℝ)) = ((η ^ (1 : ℝ))⁻¹) := Real.rpow_neg (le_of_lt hη) 1
  have e4 : η ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))
      = ((η ^ (-((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ)))))⁻¹) := by
    simpa using Real.rpow_neg (le_of_lt hη) (-((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))))
  have hG : η ^ (-(1 : ℝ)) ≤ η ^ ((m : ℝ) / 2 - (((j + m - 1 : ℕ) : ℝ))) := by
    rw [e3, e4]
    refine (inv_le_inv₀ (Real.rpow_pos_of_pos hη 1) (Real.rpow_pos_of_pos hη _)).mpr ?_
    exact Real.rpow_le_rpow_of_exponent_ge hη hη1 (by linarith [hE])
  have hX : (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * K ^ (-(((j + m - 1 : ℕ) : ℝ)))
        * η ^ (-(1 : ℝ))
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * (θ / K) ^ ((m : ℝ) / 2) :=
    le_trans (mul_le_mul_of_nonneg_left hG (by positivity)) hfin
  have hz : (θ / K) ^ ((m : ℝ) / 2) * (θ / K) ^ (-((m : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add (div_pos hθ hK), add_neg_cancel, Real.rpow_zero]
  have hX2 : (ηc / (2 * Real.exp 1)) ^ (j + m - 1) * K ^ (-(((j + m - 1 : ℕ) : ℝ)))
        * η ^ (-(1 : ℝ)) * (θ / K) ^ (-((m : ℝ) / 2))
      ≤ Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) := by
    have h1 := mul_le_mul_of_nonneg_right hX
      (Real.rpow_nonneg (le_of_lt (div_pos hθ hK)) (-((m : ℝ) / 2)))
    have h2 : Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) * (θ / K) ^ ((m : ℝ) / 2)
          * (θ / K) ^ (-((m : ℝ) / 2))
        = Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) := by
      rw [mul_assoc, hz, mul_one]
    rwa [h2] at h1
  have hX3 : cj * c1 * ((ηc / (2 * Real.exp 1)) ^ (j + m - 1)
        * K ^ (-(((j + m - 1 : ℕ) : ℝ))) * η ^ (-(1 : ℝ)) * (θ / K) ^ (-((m : ℝ) / 2)))
      ≤ cj * c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) :=
    mul_le_mul_of_nonneg_left hX2 (by positivity)
  have heq : (cj * c1 * (ηc / (2 * Real.exp 1)) ^ (j + m - 1) / (CcardR * CcntR)
        * K ^ (-(((j + m - 1 : ℕ) : ℝ))))
      * η ^ (-(1 : ℝ)) * (CcardR * (θ / K) ^ (-(m : ℝ) / 2) * CcntR)
      = cj * c1 * ((ηc / (2 * Real.exp 1)) ^ (j + m - 1)
        * K ^ (-(((j + m - 1 : ℕ) : ℝ))) * η ^ (-(1 : ℝ)) * (θ / K) ^ (-((m : ℝ) / 2))) := by
    field_simp
  rw [heq]; exact hX3

/-! ## The tube inequality at a standard stratum -/

theorem gaeTube (j m : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m))
    (hCov : ∀ k, 2 ≤ k → k < j + m → Submission.Mostow.CovolLB k) (hj : j ≠ 1)
    (hjm : 4 ≤ j + m) (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : Subgroup (PO (j + m) 1)) (D : Set (E (j + m))) (z : E (j + m))
      (η : ℝ) (R : E m ≃ₗᵢ[ℝ] E m),
      IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (j + m)) →
      0 < η → η ≤ 1 → blk j m 1 R ∈ Λ → (∀ w, R w = w → w = 0) → 0 < rotN R →
      rotN R ≤ K * η →
      (∀ c : PO (j + m) 1, c ∈ Λ → c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
        resStd j m c = 1 → c ≠ 1 → rotN R ≤ K * rotN (nrmStd j m c)) →
      ENNReal.ofReal (C * η ^ (-(1 : ℝ))) ≤ volH (j + m) D := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    refine ⟨1, one_pos, ?_⟩
    intro Λ D z η R hdisc hD hη0 hη1 hb hfree hrot hθη hsep
    exfalso
    have hR1 : R = LinearIsometryEquiv.refl ℝ (E 0) :=
      LinearIsometryEquiv.ext (fun w => Subsingleton.elim _ _)
    rw [hR1, rotN_refl] at hrot
    exact lt_irrefl 0 hrot
  · obtain ⟨ηc, hηcpos, Ccnt, hCcnt⟩ := ftbConjCount (j + m) (by omega) hA hI
    set Ct : ℕ := max Ccnt 1 with hCtdef
    have hCtpos : 0 < Ct := lt_of_lt_of_le one_pos (le_max_right Ccnt 1)
    have hCtposR : (0 : ℝ) < (Ct : ℝ) := by exact_mod_cast hCtpos
    obtain ⟨Ccard, hCcardpos, hCcard⟩ := p_cardK j m hAj hIj hA hI
    obtain ⟨vN, hvNpos, hvN⟩ := covolLB_all (j + m) (by omega)
    have hcovj : CovolLB j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; exact p_covolLB_zero
      · exact hCov j (by omega) (by omega)
    obtain ⟨cj, hcjpos, hcj⟩ := hcovj
    obtain ⟨c1, c2, hc1pos, hc2pos, hTM⟩ := tubeMeasure_ball2 j m hmpos (by omega)
    have hs : 1 ≤ (j : ℝ) + (m : ℝ) / 2 - 1 := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have h4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 4 ≤ m)
        have h5 : (2 : ℝ) ≤ (m : ℝ) / 2 := by linarith
        simp only [Nat.cast_zero, zero_add]
        linarith
      · have hj2 : (2 : ℝ) ≤ (j : ℝ) := by
          have h : 2 ≤ j := by omega
          exact_mod_cast h
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
    set θlim : ℝ := ηc / (2 * Real.sinh 2) with hθlimdef
    have hθlimpos : 0 < θlim := by
      rw [hθlimdef]
      refine div_pos hηcpos ?_
      have h := Real.sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < 2)
      linarith
    set cA : ℝ := cj * c1 * (ηc / (2 * Real.exp 1)) ^ (j + m - 1)
      / ((Ccard : ℝ) * (Ct : ℝ)) with hcAdef
    have hcApos : 0 < cA := by
      rw [hcAdef]
      refine div_pos (mul_pos (mul_pos hcjpos hc1pos) (pow_pos (div_pos hηcpos (by positivity)) _))
        (mul_pos hCcardpos hCtposR)
    refine ⟨min (cA * K ^ (-(((j + m - 1 : ℕ) : ℝ)))) (vN * θlim / K), ?_, ?_⟩
    · exact lt_min (mul_pos hcApos (Real.rpow_pos_of_pos hK _))
        (div_pos (mul_pos hvNpos hθlimpos) hK)
    intro Λ D z η R hdisc hD hη0 hη1 hb hfree hrot hθη hsep
    by_cases hsmall : rotN R ≤ θlim
    · -- ## Case A: the rotation is small enough to make a wide tube
      set θ : ℝ := rotN R with hθdef
      have hθpos : 0 < θ := hrot
      have hθηθ : θ ≤ K * η := hθη
      have hsinh2 : Real.sinh 2 ≤ ηc / (2 * θ) := by
        have h2 : θ ≤ ηc / (2 * Real.sinh 2) := hsmall
        have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sinh 2)).mp h2
        have h1 : θ * (2 * Real.sinh 2) ≤ ηc := h3
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * θ)]
        linarith
      set ρ : ℝ := Real.arsinh (ηc / (2 * θ)) - 1 with hρdef
      have hρge : 1 ≤ ρ := by
        rw [hρdef]
        have h4 : Real.arsinh (Real.sinh 2) ≤ Real.arsinh (ηc / (2 * θ)) :=
          Real.arsinh_le_arsinh.mpr hsinh2
        rw [Real.arsinh_sinh] at h4
        linarith
      have hρpos : 0 ≤ ρ := le_trans zero_le_one hρge
      have hρest : ηc / (2 * Real.exp 1 * θ) ≤ Real.exp ρ := by
        have h1 : Real.exp ρ =
            (ηc / (2 * θ) + Real.sqrt ((ηc / (2 * θ)) ^ 2 + 1)) / Real.exp 1 := by
          rw [hρdef, Real.exp_sub, Real.exp_arsinh]
          ring
        have h2 : ηc / (2 * θ) ≤ ηc / (2 * θ) + Real.sqrt ((ηc / (2 * θ)) ^ 2 + 1) :=
          le_add_of_nonneg_right (Real.sqrt_nonneg _)
        have h3 : ηc / (2 * Real.exp 1 * θ) = (ηc / (2 * θ)) / Real.exp 1 := by
          rw [div_div]
          congr 1
          ring
        rw [h1, h3]
        exact div_le_div_of_nonneg_right h2 (le_of_lt (Real.exp_pos 1))
      have htsinh : 2 * Real.sinh (ρ + 1) * θ ≤ ηc := by
        have h1 : Real.sinh (ρ + 1) = ηc / (2 * θ) := by
          rw [hρdef]
          have h2 : Real.arsinh (ηc / (2 * θ)) - 1 + 1 = Real.arsinh (ηc / (2 * θ)) := by ring
          rw [h2, Real.sinh_arsinh]
        have h2 : 2 * (ηc / (2 * θ)) * θ = ηc := by
          rw [show 2 * (ηc / (2 * θ)) * θ = (ηc / (2 * θ)) * (2 * θ) by ring]
          exact div_mul_cancel₀ ηc (by positivity)
        exact le_of_eq (by rw [h1]; exact h2)
      have htube := tube_nearId j m hAj hIj hA hI R ρ ηc hρpos hηcpos htsinh
      -- the two fundamental domains
      set CZ : Subgroup (PO (j + m) 1) :=
        Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ⊓ Λ with hCZdef
      have hdiscC : IsDiscrete (SetLike.coe CZ) := IsDiscrete.mono hdisc (fun x hx => hx.2)
      obtain ⟨Dc, hDc⟩ := gae_exists_fundamentalDomain_gen (j + m) hA hI CZ hdiscC
      set ΓY : Subgroup (PO j 1) := Subgroup.closure (resStd j m '' (CZ : Set (PO (j + m) 1)))
        with hΓYdef
      have hstab : ∀ c ∈ CZ, c ∈ SetStabStd j m :=
        fun c hc => p_centralizer_mem_SetStabStd hAj hIj hA hI R hfree hc.1
      have hΓYdisc : IsDiscrete (SetLike.coe ΓY) :=
        ((resStdDiscreteStrata j m hAj hIj hA hI).2 CZ hdiscC hstab).1
      obtain ⟨DY, hDY⟩ := gae_exists_fundamentalDomain_gen j hAj hIj ΓY hΓYdisc
      have hblk : ∀ c ∈ CZ, ∀ (v : E j) (w : E m),
          (c : PO (j + m) 1) • fermi j m v w =
            fermi j m (resStd j m (c : PO (j + m) 1) • v) (nrmStd j m (c : PO (j + m) 1) w) :=
        fun c hc v w => centralizer_acts_fermi j m hAj hIj hA hI R hfree c hc.1 v w
      have hQ := ftbTubeQuot j m hAj hIj hA hI Λ R Dc DY ρ hρpos hdisc hb hfree hblk hDc hDY
      -- the unfolding bound
      have hcount : ∀ w : E (j + m), NearIdAt (blk j m 1 R) w ηc →
          {c : PO (j + m) 1 |
            NearIdAt c w ηc ∧ ∃ γ ∈ Λ, c = γ⁻¹ * (blk j m 1 R) * γ}.ncard ≤ Ct := by
        intro w hw
        have hfix : (blk j m 1 R) • (coordEmb j m 0) = coordEmb j m 0 := by
          rw [← p_fermi_zero j m (0 : E j),
            blk_smul_fermi j m hAj hIj hA hI 1 R 0 0, hAj.2.2.2.1, R.map_zero,
            p_fermi_zero j m (0 : E j)]
        exact le_trans (hCcnt Λ (blk j m 1 R) hdisc hb ⟨coordEmb j m 0, hfix⟩ w hw).2
          (le_max_left Ccnt 1)
      have hunf := p_ftbUnfoldGen j m hAj hIj hA hI ηc hηcpos Λ D Dc (blk j m 1 R) Ct
        hdisc hD hb hDc hcount
      have hsub : tube j m ρ ∩ Dc ⊆ {u : E (j + m) | NearIdAt (blk j m 1 R) u ηc} ∩ Dc :=
        fun u hu => ⟨htube u hu.1, hu.2⟩
      have hint : volH (j + m) (tube j m ρ ∩ Dc) ≤ (Ct : ENNReal) * volH (j + m) D :=
        le_trans (measure_mono hsub) hunf
      -- the cardinality bound
      have hv : 0 < θ / K := div_pos hθpos hK
      have hv1 : θ / K ≤ 1 := by
        rw [div_le_one hK]
        calc θ ≤ K * η := hθηθ
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left hη1 (le_of_lt hK)
          _ = K := mul_one K
      have hsep' : ∀ c : PO (j + m) 1, c ∈ Λ →
          c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
          resStd j m c = 1 → c ≠ 1 → θ / K ≤ rotN (nrmStd j m c) := by
        intro c h1 h2 h3 h4
        have h5 : rotN R ≤ K * rotN (nrmStd j m c) := hsep c h1 h2 h3 h4
        rw [div_le_iff₀ hK, hθdef]
        linarith
      have hKcard := hCcard Λ R (θ / K) hdisc hb hfree hv hv1 hsep'
      -- the lower bounds
      have hTMlow : ENNReal.ofReal (c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ)) ≤
          tubeMeasure j m (Metric.closedBall 0 ρ) := by
        have h := (hTM ρ hρge).1
        rwa [show (((j + m : ℕ) : ℝ) - 1) * ρ = (((j + m - 1 : ℕ) : ℝ)) * ρ by
          rw [Nat.cast_sub (by omega : 1 ≤ j + m)]; push_cast; ring] at h
      have hDYlow : ENNReal.ofReal cj ≤ volH j DY := hcj ΓY hΓYdisc DY hDY
      have hApos : (0 : ℝ) ≤ Ccard * (θ / K) ^ (-(m : ℝ) / 2) :=
        mul_nonneg (le_of_lt hCcardpos) (Real.rpow_nonneg (le_of_lt (div_pos hθpos hK)) _)
      have hcomb : ENNReal.ofReal (cj * c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ)) ≤
          ENNReal.ofReal (Ccard * (θ / K) ^ (-(m : ℝ) / 2) * (Ct : ℝ)) * volH (j + m) D := by
        have h1 : ENNReal.ofReal (cj * c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ)) =
            ENNReal.ofReal cj *
              ENNReal.ofReal (c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ)) := by
          rw [mul_assoc]
          exact ENNReal.ofReal_mul (le_of_lt hcjpos)
        rw [h1]
        refine le_trans (mul_le_mul hDYlow hTMlow zero_le' zero_le') ?_
        refine le_trans hQ ?_
        refine le_trans (mul_le_mul hKcard hint zero_le' zero_le') ?_
        rw [show (Ct : ENNReal) = ENNReal.ofReal (Ct : ℝ) from (ENNReal.ofReal_natCast Ct).symm,
          ← mul_assoc, ← ENNReal.ofReal_mul hApos]
      -- the real arithmetic
      have hQpos : 0 < Ccard * (θ / K) ^ (-(m : ℝ) / 2) * (Ct : ℝ) :=
        mul_pos (mul_pos hCcardpos (Real.rpow_pos_of_pos (div_pos hθpos hK) _)) hCtposR
      have hfinal : ENNReal.ofReal (cj * c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) /
              (Ccard * (θ / K) ^ (-(m : ℝ) / 2) * (Ct : ℝ))) ≤ volH (j + m) D := by
        rw [ENNReal.ofReal_div_of_pos hQpos]
        rw [ENNReal.div_le_iff_le_mul (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hQpos)))
          (Or.inl ENNReal.ofReal_ne_top)]
        rw [mul_comm (ENNReal.ofReal (Ccard * (θ / K) ^ (-(m : ℝ) / 2) * (Ct : ℝ)))
          (volH (j + m) D)] at hcomb
        exact hcomb
      have hreal : min (cA * K ^ (-(((j + m - 1 : ℕ) : ℝ)))) (vN * θlim / K) * η ^ (-(1 : ℝ)) ≤
          cj * c1 * Real.exp (((j + m - 1 : ℕ) : ℝ) * ρ) /
            (Ccard * (θ / K) ^ (-(m : ℝ) / 2) * (Ct : ℝ)) := by
        have hkey := p_key j m cj c1 (Ct : ℝ) (Ccard : ℝ) ηc K η θ ρ hcjpos hc1pos
          hCtposR hCcardpos hηcpos hK hη0 hη1 hθpos hθηθ (by omega) hs hρest
        rw [le_div_iff₀ hQpos]
        refine le_trans ?_ hkey
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (le_of_lt hη0) _))
          (by positivity)
      exact le_trans (ENNReal.ofReal_le_ofReal hreal) hfinal
    · -- ## Case B: the rotation is large, use the covolume bound
      have hbig : θlim < rotN R := lt_of_not_ge hsmall
      have h1 : θlim < K * η := lt_of_lt_of_le hbig hθη
      have h3 : η⁻¹ < K / θlim := by
        rw [lt_div_iff₀ hθlimpos, mul_comm]
        exact (div_lt_iff₀ hη0).mpr h1
      have hgoal : min (cA * K ^ (-(((j + m - 1 : ℕ) : ℝ)))) (vN * θlim / K)
          * η ^ (-(1 : ℝ)) ≤ vN := by
        have hle : min (cA * K ^ (-(((j + m - 1 : ℕ) : ℝ)))) (vN * θlim / K) ≤ vN * θlim / K :=
          min_le_right _ _
        rw [show η ^ (-(1 : ℝ)) = η⁻¹ from Real.rpow_neg_one η]
        calc min (cA * K ^ (-(((j + m - 1 : ℕ) : ℝ)))) (vN * θlim / K) * η⁻¹
            ≤ (vN * θlim / K) * η⁻¹ :=
              mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (le_of_lt hη0))
          _ ≤ (vN * θlim / K) * (K / θlim) :=
              mul_le_mul_of_nonneg_left (le_of_lt h3) (by positivity)
          _ = vN := by field_simp
      exact le_trans (ENNReal.ofReal_le_ofReal hgoal) (hvN Λ hdisc D hD)

end

end Work.Mostow

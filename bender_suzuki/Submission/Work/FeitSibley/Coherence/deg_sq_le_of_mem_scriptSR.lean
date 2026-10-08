import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.CharPrelim.ft4_1
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.PGroup.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

set_option linter.style.haveILetI false

/-- **Extraction of the inducing character of `Q`.**  A character `χ ∈ 𝒮(R)` (irreducible on
`H`, non-trivial on `Q₁`, trivial on `R`) is induced from a character `φ ∈ Irr Q` which is
itself trivial on `R`, and its degree is `|D| · φ(1)`. -/
theorem exists_indQH_of_mem_scriptSR {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {R : Subgroup G} (hR : R ≤ h.S) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R) :
    ∃ φ ∈ Work.CharCore.Irr ↥h.Q,
      (∀ x : ↥h.Q, (x : G) ∈ R → φ x = φ 1) ∧
      χ = h.indQH φ ∧
      (Work.CharCore.irrDeg χ : ℝ) = (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg φ : ℝ) := by
  classical
  obtain ⟨hscriptS, hRtriv⟩ := (mem_scriptSR_iff h R).mp hχ
  obtain ⟨φ, hφ, -, hχeq⟩ := (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hscriptS
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := by
    have := hscriptS
    rw [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]
      at this
    exact this.1
  have hχC : χ ∈ Work.Clifford.Irr ↥h.H :=
    (Work.Clifford.corr_mem_Irr_charCore).mpr hχIrr
  have hIrr' : h.indQH φ ∈ Work.Clifford.Irr ↥h.H := by rw [← hχeq]; exact hχC
  have hcf : Work.CharCore.IsClassFun (h.indQH φ) := by
    rw [← hχeq]; exact Work.CharCore.isClassFun_of_mem_Irr hχIrr
  have hpull : Work.FeitSibley.CharQ.pull h φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    Work.FeitSibley.CharQ.pull_mem_Irr h hφ
  -- Frobenius reciprocity: `pull h φ` is a constituent of `χ|_Q`
  have hc : Work.Clifford.IsConstituentOf (Work.FeitSibley.CharQ.pull h φ)
      (Work.Clifford.resFun (h.Q.subgroupOf h.H) χ) := by
    rw [hχeq, Work.Clifford.IsConstituentOf]
    have hB : Work.Clifford.cfInner (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ))
        (Work.FeitSibley.CharQ.pull h φ) = 1 := by
      rw [Work.Clifford.cfInner_conj_symm]
      have hA := Work.Clifford.cfInner_indFun (Work.FeitSibley.CharQ.pull h φ) hcf
      rw [← hA, ← Work.FeitSibley.CharQ.indQH_eq_indFun,
        Work.Clifford.cfInner_eq_ite_of_mem_Irr hIrr' hIrr']
      simp
    rw [hB]
    simp
  refine ⟨φ, hφ, ?_, hχeq, ?_⟩
  · intro x hx
    have hxH : χ (((Work.FeitSibley.CharQ.toQ h x : ↥(h.Q.subgroupOf h.H)) : ↥h.H)) = χ 1 :=
      hRtriv _ (by rw [Work.FeitSibley.CharQ.toQ_coe]; exact hx)
    have h1 := Work.FeitSibley.CharQ.apply_eq_one_of_constituent h hχIrr hpull hc hxH
    rwa [Work.FeitSibley.CharQ.pull_toQ, Work.FeitSibley.CharQ.pull_one] at h1
  · have hdeg : Work.Clifford.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
        = (Nat.card h.D : ℂ) * (φ 1) := by
      change Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
        = (Nat.card h.D : ℂ) * (φ 1)
      rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one, index_subgroupOf_Q h]
    have h1 : χ 1 = (Nat.card h.D : ℂ) * (φ 1) := by
      rw [hχeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
      exact hdeg
    have hnat : Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg φ := by
      have hc : ((Work.CharCore.irrDeg χ : ℕ) : ℂ)
          = ((Nat.card h.D * Work.CharCore.irrDeg φ : ℕ) : ℂ) := by
        rw [Nat.cast_mul, ← Work.CharCore.irrDeg_spec hχIrr, h1,
          Work.CharCore.irrDeg_spec hφ]
      exact Nat.cast_inj.mp hc
    rw [hnat]
    push_cast
    ring

/-- **Isaacs 2.30 with a central section.**  Let `φ ∈ Irr Q` be trivial on `R ≤ Q` and let
`T ≤ S` satisfy `⁅S,T⁆ ≤ R`.  Then `φ(1)² · |T| · |Z| ≤ |Q|`, where `Z = [Q₁,Q₁] ∩ Z(Q₁)`.

The image of `T` in `Q/R` is central (`[Q,T] ≤ R`: `Q = S·Q₁`, `[S,T] ≤ R` by hypothesis and
`Q₁` commutes with `T ≤ S`), and so is the image of `Z` (`Z ≤ Z(Q)`); the two intersect
trivially (`T ∩ Z ≤ S ∩ Q₁ = 1`).  Passing to `Q/R`, where `φ` becomes an irreducible
character of degree `φ(1)`, its modulus is `φ(1)` on every central element
(`Work.CharPrelim.norm_char_eq_irrDeg_of_mem_center`), hence on all `|T|·|Z|` products
`t·z`; comparing with `∑_{q ∈ Q} ‖φ q‖² = |Q|` gives the claim. -/
theorem irrDeg_sq_mul_card_le_card_Q {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R T : Subgroup G) (hT : T ≤ h.S) (hRT : R ≤ T) (hcent : ⁅h.S, T⁆ ≤ R)
    {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (htriv : ∀ x : ↥h.Q, (x : G) ∈ R → φ x = φ 1) :
    (Work.CharCore.irrDeg φ : ℝ) ^ 2 *
      ((Nat.card T : ℝ) * (Nat.card (FSZ h) : ℝ)) ≤ (Nat.card h.Q : ℝ) := by
  classical
  -- elementwise commutators inside `Q` and inside `G`
  letI : Bracket ↥h.Q ↥h.Q := commutatorElement
  letI : Bracket G G := commutatorElement
  -- `Z ≤ Q₁ ≤ Q`
  have hZQ1 : FSZ h ≤ h.Q1 :=
    (inf_le_left.trans (Subgroup.commutator_le_sup h.Q1 h.Q1)).trans (le_of_eq (sup_idem h.Q1))
  have hZQ : FSZ h ≤ h.Q := hZQ1.trans h.Q1_le_Q
  -- **(1)** `[Q,T] ≤ R`
  have hQT : ⁅h.Q, T⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro q hq t ht
    obtain ⟨s, hs, q1, hq1, hsq1⟩ := h.mem_Q_decomp hq
    have h1 : ⁅q1, t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (h.commute t (hT ht) q1 hq1).symm
    rw [hsq1, commutatorElement_mul_left_eq_conj_mul, h1, mul_one]
    have h2 := hcent (Subgroup.commutator_mem_commutator hs ht)
    convert h2 using 1
    group
  have hTQ : ⁅T, h.Q⁆ ≤ R := by rw [Subgroup.commutator_comm]; exact hQT
  -- **(2)** `R ⊴ Q`
  have hQR : ⁅h.Q, R⁆ ≤ R := (Subgroup.commutator_mono_right hRT).trans hQT
  haveI hRgN : (R.subgroupOf h.Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_comm]
      exact hQR)
  -- **(3)** `Z ≤ Z(Q)`
  have hZcen : (FSZ h).subgroupOf h.Q ≤ Subgroup.center ↥h.Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    have hzZ : (z : G) ∈ FSZ h := Subgroup.mem_subgroupOf.mp hz
    have hzQ1 : (z : G) ∈ h.Q1 := hZQ1 hzZ
    have hzc : (z : G) ∈ Subgroup.centralizer (h.Q1 : Set G) := (Subgroup.mem_inf.mp hzZ).2
    apply Subtype.ext
    show (y : G) * (z : G) = (z : G) * (y : G)
    obtain ⟨s, hs, q1, hq1, hsq1⟩ := h.mem_Q_decomp y.2
    rw [hsq1]
    have h1 : Commute s (z : G) := h.commute s hs (z : G) hzQ1
    have h2 : Commute q1 (z : G) := Subgroup.mem_centralizer_iff.mp hzc q1 hq1
    exact (Commute.mul_left h1 h2).eq
  -- **(4)** descend `φ` to `Q/R`
  haveI hQfin : Fintype (↥h.Q ⧸ R.subgroupOf h.Q) := QuotientGroup.fintype _
  obtain ⟨φ', hφ', hφ'infl⟩ :=
    Work.CohApps.exists_irr_quotient_of_le_ker (R.subgroupOf h.Q) hφ
      (fun x hx => htriv x (Subgroup.mem_subgroupOf.mp hx))
  have hφ'deg : Work.CharCore.irrDeg φ' = Work.CharCore.irrDeg φ := by
    rw [← Work.CohApps.irrDeg_inflateFun (R.subgroupOf h.Q) hφ', hφ'infl]
  have hφ'infl' : ∀ w : ↥h.Q, φ w = φ' (QuotientGroup.mk' (R.subgroupOf h.Q) w) :=
    fun w => by rw [← hφ'infl]; rfl
  -- **(5)** `T` and `Z` have central image in `Q/R`
  have hTcent : ∀ x : ↥h.Q, x ∈ T.subgroupOf h.Q → ∀ y : ↥h.Q,
      QuotientGroup.mk' (R.subgroupOf h.Q) x * QuotientGroup.mk' (R.subgroupOf h.Q) y
        = QuotientGroup.mk' (R.subgroupOf h.Q) y * QuotientGroup.mk' (R.subgroupOf h.Q) x := by
    intro x hx y
    have hxy : ⁅x, y⁆ ∈ R.subgroupOf h.Q := by
      rw [Subgroup.mem_subgroupOf]
      show ⁅(x : G), (y : G)⁆ ∈ R
      exact hTQ (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx) y.2)
    have hk : QuotientGroup.mk' (R.subgroupOf h.Q) ⁅x, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff (N := R.subgroupOf h.Q) ⁅x, y⁆).mpr hxy
    rw [map_commutatorElement] at hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hk
  have hZcent : ∀ z : ↥h.Q, z ∈ (FSZ h).subgroupOf h.Q → ∀ y : ↥h.Q,
      QuotientGroup.mk' (R.subgroupOf h.Q) z * QuotientGroup.mk' (R.subgroupOf h.Q) y
        = QuotientGroup.mk' (R.subgroupOf h.Q) y * QuotientGroup.mk' (R.subgroupOf h.Q) z := by
    intro z hz y
    have hzy : y * z = z * y := Subgroup.mem_center_iff.mp (hZcen hz) y
    calc QuotientGroup.mk' (R.subgroupOf h.Q) z * QuotientGroup.mk' (R.subgroupOf h.Q) y
        = QuotientGroup.mk' (R.subgroupOf h.Q) (z * y) := (map_mul _ z y).symm
      _ = QuotientGroup.mk' (R.subgroupOf h.Q) (y * z) := by rw [← hzy]
      _ = QuotientGroup.mk' (R.subgroupOf h.Q) y * QuotientGroup.mk' (R.subgroupOf h.Q) z :=
            map_mul _ y z
  -- **(6)** `‖φ (t · z)‖ = φ(1)` for all `t ∈ T`, `z ∈ Z`
  have hval : ∀ (x : ↥h.Q), x ∈ T.subgroupOf h.Q → ∀ (z : ↥h.Q),
      z ∈ (FSZ h).subgroupOf h.Q → ‖φ (x * z)‖ = (Work.CharCore.irrDeg φ : ℝ) := by
    intro x hx z hz
    have hcentral : QuotientGroup.mk' (R.subgroupOf h.Q) (x * z) ∈
        Subgroup.center (↥h.Q ⧸ R.subgroupOf h.Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf h.Q) y
      rw [map_mul]
      have h1 : Commute (QuotientGroup.mk' (R.subgroupOf h.Q) x) y₀ := hTcent x hx y₀
      have h2 : Commute (QuotientGroup.mk' (R.subgroupOf h.Q) z) y₀ := hZcent z hz y₀
      exact (h1.mul_left h2).eq.symm
    rw [hφ'infl' (x * z),
      Work.CharPrelim.norm_char_eq_irrDeg_of_mem_center hφ' hcentral, hφ'deg]
  -- **(7)** `T ∩ Z = 1`, so the products `t · z` are `|T| · |Z|` distinct elements of `Q`
  have hbot : T.subgroupOf h.Q ⊓ (FSZ h).subgroupOf h.Q = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxT, hxZ⟩ := Subgroup.mem_inf.mp hx
    have h1 : (x : G) ∈ h.S ⊓ h.Q1 :=
      Subgroup.mem_inf.mpr ⟨hT (Subgroup.mem_subgroupOf.mp hxT),
        hZQ1 (Subgroup.mem_subgroupOf.mp hxZ)⟩
    rw [h.S_inf_Q1] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))
  have hinj : ∀ p q : ↥(T.subgroupOf h.Q) × ↥((FSZ h).subgroupOf h.Q),
      ((p.1 : ↥h.Q) * (p.2 : ↥h.Q)) = ((q.1 : ↥h.Q) * (q.2 : ↥h.Q)) → p = q := by
    rintro ⟨t1, z1⟩ ⟨t2, z2⟩ heq
    have h1 : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q)
        = (z2 : ↥h.Q) * (z1 : ↥h.Q)⁻¹ := by
      calc (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q)
          = (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) * ((z1 : ↥h.Q) * (z1 : ↥h.Q)⁻¹) := by group
        _ = (t2 : ↥h.Q)⁻¹ * ((t1 : ↥h.Q) * (z1 : ↥h.Q)) * (z1 : ↥h.Q)⁻¹ := by group
        _ = (t2 : ↥h.Q)⁻¹ * ((t2 : ↥h.Q) * (z2 : ↥h.Q)) * (z1 : ↥h.Q)⁻¹ := by rw [heq]
        _ = (z2 : ↥h.Q) * (z1 : ↥h.Q)⁻¹ := by group
    have hmem : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q)
        ∈ T.subgroupOf h.Q ⊓ (FSZ h).subgroupOf h.Q := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ t2.2) t1.2, ?_⟩
      show (((t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) : ↥h.Q) : G) ∈ FSZ h
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp z2.2)
        (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp z1.2))
    rw [hbot] at hmem
    have ht : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) = 1 := Subgroup.mem_bot.mp hmem
    have ht12 : t1 = t2 := by
      apply Subtype.ext
      simpa using congrArg (fun w => (t2 : ↥h.Q) * w) ht
    have ht12' : (t1 : ↥h.Q) = (t2 : ↥h.Q) :=
      congrArg (fun w : ↥(T.subgroupOf h.Q) => (w : ↥h.Q)) ht12
    have hz12 : z1 = z2 := by
      apply Subtype.ext
      have h2 : (t1 : ↥h.Q) * (z1 : ↥h.Q) = (t1 : ↥h.Q) * (z2 : ↥h.Q) := by
        have hh := heq
        rw [← ht12'] at hh
        exact hh
      exact mul_left_cancel h2
    exact Prod.ext ht12 hz12
  -- **(8)** the counting
  have hle' : (∑ g ∈ ((Finset.univ : Finset ↥(T.subgroupOf h.Q)).product
        (Finset.univ : Finset ↥((FSZ h).subgroupOf h.Q))).image
        (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2)
      ≤ ∑ g : ↥h.Q, ‖φ g‖ ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => by positivity)
  rw [Work.CharPrelim.sum_normSq_eq_card hφ] at hle'
  have hsum : (∑ g ∈ ((Finset.univ : Finset ↥(T.subgroupOf h.Q)).product
        (Finset.univ : Finset ↥((FSZ h).subgroupOf h.Q))).image
        (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2)
      = (Fintype.card ↥(T.subgroupOf h.Q) : ℝ) * (Fintype.card ↥((FSZ h).subgroupOf h.Q) : ℝ)
        * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun p _ q _ hpq => hinj p q hpq)]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    have hinner : ∀ x : ↥(T.subgroupOf h.Q),
        (∑ y ∈ (Finset.univ : Finset ↥((FSZ h).subgroupOf h.Q)),
            ‖φ ((x : ↥h.Q) * (y : ↥h.Q))‖ ^ 2)
          = (Fintype.card ↥((FSZ h).subgroupOf h.Q) : ℝ)
            * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => by rw [hval x x.2 y y.2])]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hcT : (Fintype.card ↥(T.subgroupOf h.Q) : ℝ) = (Nat.card T : ℝ) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT.trans h.S_le_Q)).toEquiv,
      ← Nat.card_eq_fintype_card]
  have hcZ : (Fintype.card ↥((FSZ h).subgroupOf h.Q) : ℝ) = (Nat.card (FSZ h) : ℝ) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv,
      ← Nat.card_eq_fintype_card]
  rw [hcT, hcZ] at hsum
  nlinarith [hsum, hle']

theorem deg_sq_le_of_mem_scriptSR {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R T : Subgroup G) (hR : R ≤ h.S) (hT : T ≤ h.S) (hRT : R ≤ T) (hcent : ⁅h.S, T⁆ ≤ R)
    {χ : ↥h.H → ℂ} (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R) :
    ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 ≤ (Nat.card h.D : ℝ) ^ 2 *
      (((T.subgroupOf h.S).index : ℕ) : ℝ) *
      ((Nat.card h.Q1 : ℝ) / (Nat.card (Work.FeitSibley.Coherence.FSZ h) : ℝ)) := by
  classical
  obtain ⟨φ, hφ, htriv, hχeq, hdeg⟩ := exists_indQH_of_mem_scriptSR h hR hχ
  have hcrux := irrDeg_sq_mul_card_le_card_Q h R T hT hRT hcent hφ htriv
  -- `|Q| = |S| · |Q₁|`
  have hQcard : (Nat.card h.Q : ℝ) = (Nat.card h.S : ℝ) * (Nat.card h.Q1 : ℝ) := by
    have hsup := Work.PGroup.card_sup_mul_card_inf h.S h.Q1 h.commute
    rw [h.S_sup_Q1, h.S_inf_Q1] at hsup
    have hnat : Nat.card ↥h.Q = Nat.card h.S * Nat.card h.Q1 := by simpa using hsup
    rw [hnat]
    push_cast
    ring
  -- `|S| = [S : T] · |T|`
  have hSsplit : (Nat.card h.S : ℝ) = (((T.subgroupOf h.S).index : ℕ) : ℝ) * (Nat.card T : ℝ) := by
    have h1 : Nat.card ↥(T.subgroupOf h.S) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
    have h2 : Nat.card h.S = Nat.card T * (T.subgroupOf h.S).index := by
      rw [← h1]
      exact (Subgroup.card_mul_index (T.subgroupOf h.S)).symm
    rw [h2]
    push_cast
    ring
  have hTpos : (0 : ℝ) < (Nat.card T : ℝ) := by
    haveI : Nonempty ↥T := ⟨1, T.one_mem⟩
    exact_mod_cast Nat.card_pos
  have hZpos : (0 : ℝ) < (Nat.card (FSZ h) : ℝ) := by
    haveI : Nonempty ↥(FSZ h) := ⟨1, (FSZ h).one_mem⟩
    exact_mod_cast Nat.card_pos
  -- divide the bound on `φ` by `|Z|`
  have hφbound : (Work.CharCore.irrDeg φ : ℝ) ^ 2 ≤
      (((T.subgroupOf h.S).index : ℕ) : ℝ) * (Nat.card h.Q1 : ℝ)
        / (Nat.card (FSZ h) : ℝ) := by
    rw [le_div_iff₀ hZpos]
    nlinarith [hcrux, hQcard, hSsplit, hTpos]
  rw [hdeg]
  have hmul := mul_le_mul_of_nonneg_left hφbound (sq_nonneg (Nat.card h.D : ℝ))
  calc ((Nat.card h.D : ℝ) * (Work.CharCore.irrDeg φ : ℝ)) ^ 2
      = (Nat.card h.D : ℝ) ^ 2 * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by ring
    _ ≤ (Nat.card h.D : ℝ) ^ 2 * ((((T.subgroupOf h.S).index : ℕ) : ℝ)
          * (Nat.card h.Q1 : ℝ) / (Nat.card (FSZ h) : ℝ)) := hmul
    _ = (Nat.card h.D : ℝ) ^ 2 * (((T.subgroupOf h.S).index : ℕ) : ℝ)
          * ((Nat.card h.Q1 : ℝ) / (Nat.card (FSZ h) : ℝ)) := by
        rw [div_eq_mul_inv]
        ring

end Work.FeitSibley.Coherence

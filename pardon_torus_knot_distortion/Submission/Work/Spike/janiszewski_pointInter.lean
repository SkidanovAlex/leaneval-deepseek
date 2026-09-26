import Mathlib
import Submission.Work.Smooth.JordanSeparation.componentIn_inter_componentIn

/-!
# Janiszewski's theorem for two compact plane sets meeting in a single point

`Work.Spike.janiszewski_pointInter`: if `A, B ⊆ ℂ` are compact with `A ∩ B = {z}`, and
`p, q ∉ A ∪ B` lie in the same connected component both of `Aᶜ` and of `Bᶜ`, then `p` and `q`
lie in the same connected component of `(A ∪ B)ᶜ`.

## The proof

The classical Phragmén–Brouwer argument (`Work.Smooth.JordanSeparation.componentIn_inter_componentIn`)
gives the statement for two **disjoint** *compact* sets; inspecting its proof shows that only
closedness of `A` and `B` is used, so we first record `phragmen_brouwer_closed` (disjoint *closed*
sets).

For the theorem with a single point of intersection we transport along the Möbius map
`w ↦ (w - z)⁻¹`, which sends the common point `z` to `∞`/`0` and separates the two sets:
writing `f w = (w - z)⁻¹` and `g v = z + v⁻¹` (mutually inverse on `ℂ ∖ {z}` and `ℂ ∖ {0}`),

* `F := f '' A` and `G := f '' (B \ {z})` are closed, disjoint, and `Fᶜ = f '' Aᶜ`,
* `p' = f p`, `q' = f q` lie in the same component of `Fᶜ` and of `Gᶜ`,
* `(F ∪ G)ᶜ = f '' (A ∪ B)ᶜ`.

Phragmén–Brouwer (closed case) then connects `p'` and `q'` inside `f '' (A ∪ B)ᶜ`, and applying
`g` transports the connection back to `(A ∪ B)ᶜ`.
-/

open Set

namespace Work.Spike

noncomputable section

/-! ## Phragmén–Brouwer for two disjoint closed plane sets -/

/-- **Phragmén–Brouwer / Alexander's lemma, closed form.**  For disjoint closed `A B ⊆ ℂ` and
`x ∉ A ∪ B`, the intersection of the components of `x` in `Aᶜ` and in `Bᶜ` is the component of `x`
in `(A ∪ B)ᶜ`. -/
theorem phragmen_brouwer_closed {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) {x : ℂ} (hx : x ∉ A ∪ B) :
    connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x = connectedComponentIn (A ∪ B)ᶜ x := by
  have hAcl : IsClosed A := hA
  have hBcl : IsClosed B := hB
  have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
  have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
  have hsubA : connectedComponentIn (A ∪ B)ᶜ x ⊆ connectedComponentIn Aᶜ x :=
    connectedComponentIn_mono x (fun z hz hzA => hz (Or.inl hzA))
  have hsubB : connectedComponentIn (A ∪ B)ᶜ x ⊆ connectedComponentIn Bᶜ x :=
    connectedComponentIn_mono x (fun z hz hzB => hz (Or.inr hzB))
  apply Subset.antisymm
  · intro y hy
    obtain ⟨hyA, hyB⟩ := hy
    have hyAc : y ∈ Aᶜ := connectedComponentIn_subset Aᶜ x hyA
    have hyBc : y ∈ Bᶜ := connectedComponentIn_subset Bᶜ x hyB
    obtain ⟨α, hαU⟩ : JoinedIn Aᶜ x y :=
      Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn hAcl.isOpen_compl hxA hyA
    obtain ⟨β, hβU⟩ : JoinedIn Bᶜ x y :=
      Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn hBcl.isOpen_compl hxB hyB
    have h01 : (0:ℝ) ≤ 1 := by norm_num
    set H : ℝ × ℝ → ℂ := fun p =>
      (1 - p.1) * α (Set.projIcc 0 1 h01 p.2) + p.1 * β (Set.projIcc 0 1 h01 p.2) with hH
    have hHc : Continuous H := by rw [hH]; fun_prop
    set S₁ : Set (ℝ × ℝ) := H ⁻¹' A with hS₁
    set S₂ : Set (ℝ × ℝ) := H ⁻¹' B with hS₂
    have hmS₁ : ∀ z : ℝ × ℝ, z ∈ S₁ ↔ H z ∈ A := fun z => by rw [hS₁]; rfl
    have hmS₂ : ∀ z : ℝ × ℝ, z ∈ S₂ ↔ H z ∈ B := fun z => by rw [hS₂]; rfl
    have hS₁c : IsClosed S₁ := by rw [hS₁]; exact hAcl.preimage hHc
    have hS₂c : IsClosed S₂ := by rw [hS₂]; exact hBcl.preimage hHc
    have hSdisj : Disjoint S₁ S₂ := by
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      exact Set.disjoint_left.mp hAB ((hmS₁ z).mp hz₁) ((hmS₂ z).mp hz₂)
    have hleft : ∀ v : ℝ, H (0, v) = α (Set.projIcc 0 1 h01 v) := by intro v; simp [hH]
    have hright : ∀ v : ℝ, H (1, v) = β (Set.projIcc 0 1 h01 v) := by intro v; simp [hH]
    have hp0 : Set.projIcc 0 1 h01 (0:ℝ) = (0 : Set.Icc (0:ℝ) 1) := by
      apply Subtype.ext; rw [Set.projIcc_of_mem h01 ⟨le_rfl, zero_le_one⟩]; rfl
    have hp1 : Set.projIcc 0 1 h01 (1:ℝ) = (1 : Set.Icc (0:ℝ) 1) := by
      apply Subtype.ext; rw [Set.projIcc_of_mem h01 ⟨zero_le_one, le_rfl⟩]; rfl
    have hbot : ∀ u : ℝ, H (u, 0) = x := by
      intro u; simp only [hH]; rw [hp0, α.source, β.source]; ring
    have htop : ∀ u : ℝ, H (u, 1) = y := by
      intro u; simp only [hH]; rw [hp1, α.target, β.target]; ring
    have hL : S₁ ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = α (Set.projIcc 0 1 h01 v) := by rw [hu]; exact hleft v
      exact hαU _ (hHu ▸ (hmS₁ _).mp h1)
    have hR : S₂ ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = β (Set.projIcc 0 1 h01 v) := by rw [hu]; exact hright v
      exact hβU _ (hHu ▸ (hmS₂ _).mp h1)
    have hBtm : (S₁ ∪ S₂) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = x := by rw [hv]; exact hbot u
      rcases h1 with h | h
      · exact hx (Or.inl (hHu ▸ (hmS₁ _).mp h))
      · exact hx (Or.inr (hHu ▸ (hmS₂ _).mp h))
    have hTop : (S₁ ∪ S₂) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = y := by rw [hv]; exact htop u
      rcases h1 with h | h
      · exact hyAc (hHu ▸ (hmS₁ _).mp h)
      · exact hyBc (hHu ▸ (hmS₂ _).mp h)
    have hkey : ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S₁ ∪ S₂)ᶜ ((0, 0) : ℝ × ℝ) :=
      Work.Smooth.JordanSeparation.square_lemma hS₁c hS₂c hSdisj hL hR hBtm hTop
    set K : Set (ℝ × ℝ) := connectedComponentIn (S₁ ∪ S₂)ᶜ ((0, 0) : ℝ × ℝ) with hK
    have hKpre : IsPreconnected K := by rw [hK]; exact isPreconnected_connectedComponentIn
    have hKsub : K ⊆ (S₁ ∪ S₂)ᶜ := by rw [hK]; exact connectedComponentIn_subset _ _
    have h00K : ((0, 0) : ℝ × ℝ) ∈ K := by
      rw [hK]
      refine mem_connectedComponentIn ?_
      rw [Set.mem_compl_iff, Set.mem_union, not_or, hmS₁, hmS₂]
      exact ⟨fun h => hx (Or.inl (hbot 0 ▸ h)), fun h => hx (Or.inr (hbot 0 ▸ h))⟩
    have h01K : ((0, 1) : ℝ × ℝ) ∈ K := by rw [hK]; exact hkey
    have hImpre : IsPreconnected (H '' K) := hKpre.image H hHc.continuousOn
    have hImsub : H '' K ⊆ (A ∪ B)ᶜ := by
      rintro z ⟨p, hp, rfl⟩
      have hp' := hKsub hp
      rw [Set.mem_compl_iff, Set.mem_union, not_or] at hp'
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨fun h => hp'.1 ((hmS₁ p).mpr h), fun h => hp'.2 ((hmS₂ p).mpr h)⟩
    have hxIm : x ∈ H '' K := ⟨(0, 0), h00K, hbot 0⟩
    have hfin := hImpre.subset_connectedComponentIn hxIm hImsub
    exact hfin ⟨(0, 1), h01K, htop 0⟩
  · intro y hy
    exact ⟨hsubA hy, hsubB hy⟩


/-! ## The Möbius coordinate `w ↦ (w - z)⁻¹` -/

/-- The Möbius map `w ↦ (w - z)⁻¹` (with the convention `0⁻¹ = 0`). -/
def Psi (z : ℂ) : ℂ → ℂ := fun w => (w - z)⁻¹

/-- The inverse of `Psi z`, namely `v ↦ z + v⁻¹` (with `0⁻¹ = 0`). -/
def PsiInv (z : ℂ) : ℂ → ℂ := fun v => z + v⁻¹

@[simp] theorem Psi_apply (z w : ℂ) : Psi z w = (w - z)⁻¹ := rfl
@[simp] theorem PsiInv_apply (z v : ℂ) : PsiInv z v = z + v⁻¹ := rfl

theorem PsiInv_Psi (z s : ℂ) : PsiInv z (Psi z s) = s := by
  simp only [Psi_apply, PsiInv_apply]
  rw [inv_inv]; ring

theorem Psi_PsiInv (z v : ℂ) : Psi z (PsiInv z v) = v := by
  simp only [Psi_apply, PsiInv_apply]
  rw [show z + v⁻¹ - z = v⁻¹ by ring, inv_inv]

theorem PsiInv_zero (z : ℂ) : PsiInv z 0 = z := by
  simp [PsiInv_apply]

theorem Psi_zero (z : ℂ) : Psi z z = 0 := by
  simp [Psi_apply]

theorem continuousOn_Psi (z : ℂ) : ContinuousOn (Psi z) ({z}ᶜ : Set ℂ) := by
  rw [show Psi z = fun w : ℂ => (w - z)⁻¹ from rfl]
  exact (continuous_id.continuousOn.sub continuousOn_const).inv₀ (fun w hw => sub_ne_zero.mpr hw)

theorem continuousOn_PsiInv (z : ℂ) : ContinuousOn (PsiInv z) ({0}ᶜ : Set ℂ) := by
  rw [show PsiInv z = fun v : ℂ => z + v⁻¹ from rfl]
  exact continuousOn_const.add continuousOn_inv₀

theorem preimage_compl_Psi (z : ℂ) (S : Set ℂ) :
    (Psi z '' S)ᶜ = PsiInv z ⁻¹' Sᶜ := by
  ext v
  simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_preimage]
  constructor
  · intro hv hgv; exact hv ⟨PsiInv z v, hgv, Psi_PsiInv z v⟩
  · rintro hgv ⟨s, hs, hsv⟩
    have key : PsiInv z v = s := by rw [← hsv]; exact PsiInv_Psi z s
    exact hgv (key ▸ hs)

/-! ## The main theorem -/

theorem janiszewski_pointInter {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    {z : ℂ} (hz : A ∩ B = {z}) {p q : ℂ} (hp : p ∉ A ∪ B) (hq : q ∉ A ∪ B)
    (hAc : q ∈ connectedComponentIn Aᶜ p) (hBc : q ∈ connectedComponentIn Bᶜ p) :
    q ∈ connectedComponentIn (A ∪ B)ᶜ p := by
  have hAcl : IsClosed A := hA.isClosed
  have hBcl : IsClosed B := hB.isClosed
  have hzAB : z ∈ A ∩ B := by rw [hz]; rfl
  have hzA : z ∈ A := hzAB.1
  have hzB : z ∈ B := hzAB.2
  have hopen0 : IsOpen ({0}ᶜ : Set ℂ) :=
    isOpen_compl_iff.mpr (isClosed_singleton (x := (0:ℂ)))
  -- Injectivity of `Psi z`
  have hPsi_inj : Function.Injective (Psi z) := fun u v h => by
    rw [← PsiInv_Psi z u, h, PsiInv_Psi z v]
  -- `Psi z '' A` is closed
  have hFclosed : IsClosed (Psi z '' A) := isOpen_compl_iff.mp (by
    rw [preimage_compl_Psi z A]
    refine ContinuousOn.isOpen_preimage (continuousOn_PsiInv z) hopen0 ?_ hAcl.isOpen_compl
    intro v hv h0
    rw [Set.mem_preimage, h0, PsiInv_zero] at hv
    exact hv hzA)
  -- `Psi z '' (B \ {z})` is closed
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall z).mp hB.isBounded
  set Rp : ℝ := |R| + 1 with hRp
  have hRppos : 0 < Rp := by rw [hRp]; positivity
  have hRb : B ⊆ Metric.closedBall z Rp :=
    fun b hb => Metric.closedBall_subset_closedBall
      (by rw [hRp]; linarith [le_abs_self R]) (hR hb)
  have hgBc_open : IsOpen (PsiInv z ⁻¹' Bᶜ) := by
    refine ContinuousOn.isOpen_preimage (continuousOn_PsiInv z) hopen0 ?_ hBcl.isOpen_compl
    intro v hv h0
    rw [Set.mem_preimage, h0, PsiInv_zero] at hv
    exact hv hzB
  have hball : Metric.ball (0:ℂ) (1/Rp) ⊆ PsiInv z ⁻¹' Bᶜ ∪ {0} := by
    intro v hv
    by_cases hv0 : v = 0
    · exact Or.inr hv0
    · left
      rw [Set.mem_preimage]
      intro hvB
      have hvnorm : ‖v‖ < 1/Rp := by rwa [Metric.mem_ball, dist_zero_right] at hv
      have hb : ‖(z + v⁻¹) - z‖ ≤ Rp := by
        have h := hRb hvB
        rw [Metric.mem_closedBall, Complex.dist_eq] at h
        exact h
      have hb' : ‖v⁻¹‖ ≤ Rp := by rw [show z + v⁻¹ - z = v⁻¹ by ring] at hb; exact hb
      rw [norm_inv] at hb'
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have h3 : 1 ≤ Rp * ‖v‖ := by
        have hmul := mul_le_mul_of_nonneg_right hb' (norm_nonneg v)
        rwa [inv_mul_cancel₀ (ne_of_gt hvpos)] at hmul
      have h4 : 1/Rp ≤ ‖v‖ := by
        rw [div_le_iff₀ hRppos]; linarith [h3, mul_comm Rp ‖v‖]
      linarith [hvnorm, h4]
  have hne : ∀ v : ℂ, PsiInv z v ≠ z ↔ v ≠ 0 := by
    intro v
    rw [PsiInv_apply]
    constructor
    · intro h h0; exact h (by rw [h0, inv_zero, add_zero])
    · intro h hz'
      exact h (inv_eq_zero.mp (add_left_cancel (hz'.trans (add_zero z).symm)))
  have hpreG : PsiInv z ⁻¹' (B \ {z})ᶜ = PsiInv z ⁻¹' Bᶜ ∪ {0} := by
    apply Set.Subset.antisymm
    · intro v hv
      rw [Set.mem_preimage, Set.mem_compl_iff] at hv
      rw [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      by_cases h : v = 0
      · exact Or.inr h
      · refine Or.inl ?_
        by_contra hB
        exact hv (Set.mem_sdiff (PsiInv z v) |>.mpr ⟨hB, (hne v).mpr h⟩)
    · intro v hv
      rw [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hv
      rw [Set.mem_preimage, Set.mem_compl_iff]
      rcases hv with hB | h0
      · exact fun hc => hB (Set.mem_sdiff (PsiInv z v) |>.mp hc |>.1)
      · subst h0
        rw [PsiInv_zero]
        exact fun hc => (Set.mem_sdiff z |>.mp hc |>.2) rfl
  have hGclosed : IsClosed (Psi z '' (B \ {z})) := isOpen_compl_iff.mp (by
    rw [preimage_compl_Psi z (B \ {z}), hpreG]
    rw [show PsiInv z ⁻¹' Bᶜ ∪ {0} = PsiInv z ⁻¹' Bᶜ ∪ Metric.ball (0:ℂ) (1/Rp) from by
      apply Set.Subset.antisymm
      · intro v hv
        rcases hv with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h, Metric.mem_ball, dist_zero_right, norm_zero]; positivity)
      · intro v hv
        rcases hv with h | h
        · exact Or.inl h
        · exact hball h]
    exact hgBc_open.union Metric.isOpen_ball)
  -- disjointness
  have hFGdisj : Disjoint (Psi z '' A) (Psi z '' (B \ {z})) := by
    rw [Set.disjoint_left]
    rintro v ⟨a, ha, hae⟩ ⟨b, hb, hbe⟩
    obtain ⟨hbB, hbz⟩ := (Set.mem_sdiff b).mp hb
    have h1 : a = b := by rw [← PsiInv_Psi z a, hae, ← hbe, PsiInv_Psi z b]
    have haz : a = z := by
      have hmem : a ∈ A ∩ B := ⟨ha, by rw [h1]; exact hbB⟩
      rw [hz] at hmem; exact hmem
    have hbz' : b = z := by rw [← h1]; exact haz
    exact hbz hbz'
  -- union
  have hAuB : A ∪ (B \ {z}) = A ∪ B := by
    apply Set.Subset.antisymm
    · rintro x (h | h)
      · exact Or.inl h
      · exact Or.inr h.1
    · rintro x (h | h)
      · exact Or.inl h
      · by_cases hx : x = z
        · exact Or.inl (hx ▸ hzA)
        · exact Or.inr ⟨h, fun hz' => hx hz'⟩
  have hunion : Psi z '' A ∪ Psi z '' (B \ {z}) = Psi z '' (A ∪ B) := by
    rw [← Set.image_union (Psi z) A (B \ {z}), hAuB]
  -- the images of `p`
  have hpA : p ∈ Aᶜ := fun h => hp (Or.inl h)
  have hqA : q ∈ Aᶜ := fun h => hq (Or.inl h)
  have hpB : p ∈ Bᶜ := fun h => hp (Or.inr h)
  have hqB : q ∈ Bᶜ := fun h => hq (Or.inr h)
  have hpq_notin : Psi z p ∉ Psi z '' A ∪ Psi z '' (B \ {z}) := by
    rintro (⟨a, ha, hae⟩ | ⟨b, hb, hbe⟩)
    · exact hp (Or.inl (by rw [← hPsi_inj hae]; exact ha))
    · obtain ⟨hbB, hbz⟩ := (Set.mem_sdiff b).mp hb
      exact hp (Or.inr (by rw [← hPsi_inj hbe]; exact hbB))
  -- connectivity in `(Psi z '' A)ᶜ`
  have hFconn : Psi z q ∈ connectedComponentIn (Psi z '' A)ᶜ (Psi z p) := by
    have hpre : IsPreconnected (connectedComponentIn Aᶜ p) := isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn Aᶜ p ⊆ {z}ᶜ := fun w hw => by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hwz => connectedComponentIn_subset Aᶜ p hw (hwz ▸ hzA)
    have himg : IsPreconnected (Psi z '' connectedComponentIn Aᶜ p) :=
      hpre.image _ ((continuousOn_Psi z).mono hsub)
    have hmem : Psi z p ∈ Psi z '' connectedComponentIn Aᶜ p :=
      ⟨p, mem_connectedComponentIn hpA, rfl⟩
    have hsub' : Psi z '' connectedComponentIn Aᶜ p ⊆ (Psi z '' A)ᶜ := by
      rw [preimage_compl_Psi z A]
      rintro w ⟨s, hs, rfl⟩
      rw [Set.mem_preimage, PsiInv_Psi]
      exact connectedComponentIn_subset Aᶜ p hs
    exact himg.subset_connectedComponentIn hmem hsub' ⟨q, hAc, rfl⟩
  have hGconn : Psi z q ∈ connectedComponentIn (Psi z '' (B \ {z}))ᶜ (Psi z p) := by
    have hpre : IsPreconnected (connectedComponentIn Bᶜ p) := isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn Bᶜ p ⊆ {z}ᶜ := fun w hw => by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hwz => connectedComponentIn_subset Bᶜ p hw (hwz ▸ hzB)
    have himg : IsPreconnected (Psi z '' connectedComponentIn Bᶜ p) :=
      hpre.image _ ((continuousOn_Psi z).mono hsub)
    have hmem : Psi z p ∈ Psi z '' connectedComponentIn Bᶜ p :=
      ⟨p, mem_connectedComponentIn hpB, rfl⟩
    have hsub' : Psi z '' connectedComponentIn Bᶜ p ⊆ (Psi z '' (B \ {z}))ᶜ := by
      rw [preimage_compl_Psi z (B \ {z}), hpreG]
      rintro w ⟨s, hs, rfl⟩
      rw [Set.mem_union]
      left
      rw [Set.mem_preimage, PsiInv_Psi]
      exact connectedComponentIn_subset Bᶜ p hs
    exact himg.subset_connectedComponentIn hmem hsub' ⟨q, hBc, rfl⟩
  -- Phragmén–Brouwer
  have hPB := phragmen_brouwer_closed hFclosed hGclosed hFGdisj (x := Psi z p) hpq_notin
  have hfinal : Psi z q ∈ connectedComponentIn (Psi z '' A ∪ Psi z '' (B \ {z}))ᶜ (Psi z p) := by
    rw [← hPB]; exact ⟨hFconn, hGconn⟩
  rw [hunion, preimage_compl_Psi z (A ∪ B)] at hfinal
  -- transport back
  set W : Set ℂ := connectedComponentIn (PsiInv z ⁻¹' (A ∪ B)ᶜ) (Psi z p) with hWdef
  have hWpre : IsPreconnected W := by rw [hWdef]; exact isPreconnected_connectedComponentIn
  have hWsub : W ⊆ PsiInv z ⁻¹' (A ∪ B)ᶜ := by
    rw [hWdef]; exact connectedComponentIn_subset _ _
  have hWz : (Psi z p) ∈ W := by
    rw [hWdef]
    exact mem_connectedComponentIn (by rw [Set.mem_preimage, PsiInv_Psi]; exact fun h => hp h)
  have hWq : (Psi z q) ∈ W := by rw [hWdef]; exact hfinal
  have hW0 : W ⊆ {0}ᶜ := by
    intro v hv
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hv0
    have h1 := hWsub hv
    rw [Set.mem_preimage, hv0, PsiInv_zero] at h1
    exact h1 (Or.inl hzA)
  have himgW : IsPreconnected (PsiInv z '' W) :=
    hWpre.image _ ((continuousOn_PsiInv z).mono hW0)
  have hp_mem : p ∈ PsiInv z '' W := ⟨Psi z p, hWz, PsiInv_Psi z p⟩
  have hq_mem : q ∈ PsiInv z '' W := ⟨Psi z q, hWq, PsiInv_Psi z q⟩
  have hsubu : PsiInv z '' W ⊆ (A ∪ B)ᶜ := by
    rintro w ⟨v, hv, rfl⟩
    exact hWsub hv
  exact himgW.subset_connectedComponentIn hp_mem hsubu hq_mem

end

end Work.Spike

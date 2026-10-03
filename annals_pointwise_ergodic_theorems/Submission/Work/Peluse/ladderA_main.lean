import Mathlib
import Submission.Work.Peluse.LadderA.midPerQ
import Submission.Work.Peluse.LadderA.mainBookkeep
import Submission.Work.Peluse.LadderA.zeroBranch

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

lemma boxNormPow_nonneg' (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ boxNormPow t Q S f := norm_nonneg _

lemma boxNorm_nonneg (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ boxNorm t Q S f :=
  Real.rpow_nonneg (boxNormPow_nonneg' t Q S f) _

/-- Splitting a sum over the parameter box along the peeled slot, as an iterated sum over the
`a''`-part (with the `s₀`-coordinate pinned to `0`) and the peeled coordinate. -/
lemma sum_paramBox_split' (k : ι → ℕ) (M₂ : ℕ) (s₀ : Slot ι k)
    (G : (Slot ι k → ℤ) → ℝ) :
    (∑ a' ∈ paramBox (k := k) M₂, G a') =
      ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        ∑ a'' ∈ (paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0),
          G (Function.update a'' s₀ a₀) :=
  sum_paramBox_split k M₂ s₀ G

/-- The cardinality identity for the split of the parameter box. -/
lemma card_paramBox_split (k : ι → ℕ) (M₂ : ℕ) (s₀ : Slot ι k) :
    (paramBox (k := k) M₂).card =
      ((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card *
        (Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card := by
  have h1 := sum_paramBox_split k M₂ s₀ (fun _ : Slot ι k → ℤ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [h1, mul_comm]



/-- **The middle step.**  From the ladder's hypothesis (at window `N`), the good set of pairs
`(a, a'')` on which the conclusion's box norm is bounded below by `BB`. -/
theorem midBound {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ) (s₀ : Slot ι k) (m : ℕ)
    (hm : Fintype.card (FamIdx kω) = m)
    (hs1 : 1 ≤ Fintype.card (AIdx k kω s₀))
    (tbig : ℕ) (s' : ℕ) (hs' : 1 ≤ s') (C' A : ℝ) (hC' : 0 < C') (hA : 1 ≤ A)
    (Khc : ℕ) (hKhc : 1 ≤ Khc) (ht : s' + 1 ≤ tbig) (htm : m ≤ tbig)
    (hconc : ∀ (c : ℤ), 0 < c → ∀ (Nw M₁ M₂ : ℕ) (d : Fin (Fintype.card (AIdx k kω s₀)) → ℤ)
        (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ Nw → (M₁ : ℝ) * (M₂ : ℝ) ≤ (Nw : ℝ) / (c : ℝ) →
        (∀ i : Fin (Fintype.card (AIdx k kω s₀)),
            |d i| ≤ (((Fintype.card (Slot ι k)) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ)) →
        SupportIn f Nw → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ Khc → A ≤ (M₂ : ℝ) * (δ * δ') ^ Khc →
        δ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
              ∑ a ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
                boxNorm (Fintype.card (AIdx k kω s₀))
                  (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
                    arithIcc (c * a + d i) M₁) (symIcc Nw) f →
        C' * (δ * δ') ^ Khc ≤
          uNorm s' (arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc Nw) f)
    (Kbig : ℕ) (Cbig : ℝ) (c₁ : ℝ) (Kh : ℕ) (hKhc_le : Khc ≤ Kh)
    (hKbig : 2 ^ (m + 1) * Kh + 1 ≤ Kbig) (hCbig : A / c₁ ^ Khc ≤ Cbig) (hc₁ : 0 < c₁)
    (hCbig2 : 2 ≤ Cbig)
    (hδ₀ge : ∀ γ : ℝ, 0 < γ → c₁ * γ ^ (2 ^ m) ≤
      ((γ / ((((m * (Fintype.card (Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1)) / 2) ^ (2 ^ m) / 2))
    (Adata : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ)
    (hM₂pos : 1 ≤ M₂) (hM₂M₁ : M₂ ≤ M₁) (hN : 1 ≤ N) (hM₁₂ : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ))
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 < γ') (hCγ' : Cbig * γ' ≤ γ ^ Kbig)
    (hAdata : Adata.Nonempty)
    (hppos : ∀ i a, a ∈ Adata → 0 < p i a)
    (hpshift : ∀ i a, a ∈ Adata → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ))
    (hDpshift : ∀ i a, a ∈ Adata → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    (hfb : ∀ a ∈ Adata, ∀ x : ℤ, ‖f a x‖ ≤ 1) (hfsupp : ∀ a ∈ Adata, SupportIn (f a) N)
    (hnondeg : Cbig * (γ * γ') ^ (-(Kbig : ℤ)) ≤ (M₂ : ℝ))
    (hhyp : γ ≤ ((Adata.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a)) :
    ∃ G : Finset ((Fin n → ℤ) × (Slot ι k → ℤ)),
      G ⊆ Adata.product ((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)) ∧
      γ / ((((m * (Fintype.card (Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1) * 2)
        ≤ (G.card : ℝ) / ((Adata.card : ℝ) *
            (((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)) ∧
      ∀ q ∈ G, ∀ b₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        (c₁ * γ ^ (2 ^ m)) ^
            (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          (c₁ * γ ^ (2 ^ m) * γ') ^
            (Khc * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
        ≤ boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
            (fun j => conclDir p M₁ M₂ γ' s₀ tbig q.1 (Function.update q.2 s₀ b₀)
              ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) (f q.1) := by
  classical
  -- elementary consequences
  have hM₁ : 1 ≤ M₁ := le_trans hM₂pos hM₂M₁
  have hNM : M₁ ≤ N := by
    have h1 : M₁ ≤ M₁ * M₂ := Nat.le_mul_of_pos_right (m := M₂) M₁ hM₂pos
    have h2 : ((M₁ * M₂ : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
    exact le_trans h1 (by exact_mod_cast h2)
  have hM₂nn : (0 : ℝ) < (M₂ : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM₂pos
  -- the two boxes
  have hboxZne : (Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).Nonempty :=
    ⟨0, by rw [Finset.mem_Ioo]; constructor <;> omega⟩
  have hboxRne : ((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).Nonempty := by
    refine ⟨fun _ => 0, Finset.mem_filter.mpr ⟨?_, rfl⟩⟩
    rw [paramBox, Fintype.mem_piFinset]
    intro s
    rw [Finset.mem_Ioo]
    constructor <;> omega
  have hprodne : (Adata.product ((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0))).Nonempty :=
    hAdata.product hboxRne
  -- constants
  set Kb : ℕ := m * (Fintype.card (Slot ι k) * D + 1) + 1 with hKb
  set boxR : Finset (Slot ι k → ℤ) := (paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0) with hboxR
  set boxZ : Finset ℤ := Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ) with hboxZ
  set Nb : ℕ := Kb * N with hNb
  set γ₁ : ℝ := γ / ((Kb : ℝ) + 1) with hγ₁
  have hγ₁pos : 0 < γ₁ := by positivity
  -- (1) the split average
  have hsplit := hyp_avg_split k kω p D s₀ m hm Kb Adata M₁ M₂ N γ f hM₂pos hN hKb.symm hhyp
  rw [← hboxR, ← hboxZ] at hsplit
  -- rewrite as an average over the product
  have hcard : ((Adata.product boxR).card : ℝ) = (Adata.card : ℝ) * (boxR.card : ℝ) := by
    rw [show Adata.product boxR = Adata ×ˢ boxR from rfl, Finset.card_product]; push_cast; ring
  have hrewrite : (γ₁ ≤ ((Adata.card : ℝ))⁻¹ * (boxR.card : ℝ)⁻¹ * (boxZ.card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ a'' ∈ boxR, ∑ a₀ ∈ boxZ,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
              ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f a)) →
      γ₁ ≤ (((Adata.product boxR).card : ℝ))⁻¹ * ((boxZ.card : ℝ))⁻¹ *
        ∑ q ∈ Adata.product boxR, ∑ a₀ ∈ boxZ,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
              ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1) := by
    intro h
    have h2 : (∑ a ∈ Adata, ∑ a'' ∈ boxR, ∑ a₀ ∈ boxZ,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
              ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f a))
        = ∑ q ∈ Adata.product boxR, ∑ a₀ ∈ boxZ,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
              ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1) := by
      rw [show Adata.product boxR = Adata ×ˢ boxR from rfl, Finset.sum_product]
    rw [h2] at h
    calc γ₁ ≤ (Adata.card : ℝ)⁻¹ * (boxR.card : ℝ)⁻¹ * (boxZ.card : ℝ)⁻¹ * _ := h
      _ = (((Adata.product boxR).card : ℝ))⁻¹ * (boxZ.card : ℝ)⁻¹ * _ := by
            rw [hcard, mul_inv]
  have hγ₁ineq := hrewrite hsplit
  -- (2) Markov in the `a₀`-variable
  have haux := markov_density (Adata.product boxR) boxZ
    (fun q a₀ => boxNorm (Fintype.card (FamIdx kω))
      (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
        ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1))
    hprodne hboxZne
    (fun q _ a₀ _ => boxNorm_nonneg _ _ _ _)
    (fun q hq a₀ ha₀ => by
      have hqA : q.1 ∈ Adata := (Finset.mem_product.mp hq).1
      have h1 : boxNormPow (Fintype.card (FamIdx kω))
          (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
            ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1) ≤ 1 :=
        BoxNorm.boxNormPow_le_one (hfb q.1 hqA) (fun x hx => by
          apply hfsupp q.1 hqA
          have h2 : ¬ (|x| ≤ (((Kb * N : ℕ)) : ℤ)) := fun hc =>
            hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hc)
          have h3 : (((Kb * N : ℕ)) : ℤ) < |x| := lt_of_not_ge h2
          have h4 : ((N : ℤ)) ≤ (((Kb * N : ℕ)) : ℤ) := by
            have h5 : N ≤ Kb * N := Nat.le_mul_of_pos_left (n := Kb) N (by rw [hKb]; omega)
            exact_mod_cast h5
          have h7 : ((N : ℤ)) < ((x.natAbs : ℕ) : ℤ) := by
            rw [Int.natCast_natAbs]; exact lt_of_le_of_lt h4 h3
          exact_mod_cast h7)
      rw [Work.Peluse.boxNorm]
      exact Real.rpow_le_one (boxNormPow_nonneg' _ _ _ _) h1 (by positivity))
    hγ₁pos hγ₁ineq
  -- the good set
  set G : Finset ((Fin n → ℤ) × (Slot ι k → ℤ)) :=
    (Adata.product boxR).filter (fun q => γ₁ / 2 ≤ (boxZ.card : ℝ)⁻¹ *
      ∑ a₀ ∈ boxZ, boxNorm (Fintype.card (FamIdx kω))
        (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
          ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1)) with hGdef
  have hGsub : G ⊆ Adata.product boxR := Finset.filter_subset _ _
  have hGdens : γ₁ / 2 ≤ (G.card : ℝ) / ((Adata.card : ℝ) * (boxR.card : ℝ)) := by
    have haux' := haux
    have hsum : (∑ q ∈ Adata.product boxR,
        (if γ₁ / 2 ≤ (boxZ.card : ℝ)⁻¹ * ∑ a₀ ∈ boxZ, boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
            ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1)
          then (1 : ℝ) else 0)) = (G.card : ℝ) := by
      rw [hGdef, Finset.card_filter]
      push_cast
      rfl
    rw [hsum, hcard] at haux'
    calc γ₁ / 2 ≤ ((Adata.card : ℝ) * (boxR.card : ℝ))⁻¹ * (G.card : ℝ) := haux'
      _ = (G.card : ℝ) / ((Adata.card : ℝ) * (boxR.card : ℝ)) := by rw [div_eq_mul_inv, mul_comm]
  have hGgood : ∀ q ∈ G, γ₁ / 2 ≤ (boxZ.card : ℝ)⁻¹ *
      ∑ a₀ ∈ boxZ, boxNorm (Fintype.card (FamIdx kω))
        (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
          ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Kb * N)) (f q.1) :=
    fun q hq => (Finset.mem_filter.mp hq).2
  refine ⟨G, hGsub, ?_, ?_⟩
  · have hconv : γ / (((Kb : ℝ) + 1) * 2) = γ₁ / 2 := by rw [hγ₁, div_div]
    rw [hconv]
    exact hGdens
  · intro q hq b₀ hb₀
    obtain ⟨hqA, hqR⟩ := Finset.mem_product.mp (hGsub hq)
    have hnondeg' : Cbig ≤ (M₂ : ℝ) * (γ * γ') ^ Kbig := by
      have hx : (0 : ℝ) < (γ * γ') ^ Kbig := by positivity
      have hz : (γ * γ') ^ (-(Kbig : ℤ)) = ((γ * γ') ^ Kbig)⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      rw [hz] at hnondeg
      calc Cbig = Cbig * ((γ * γ') ^ Kbig)⁻¹ * (γ * γ') ^ Kbig := by field_simp
        _ ≤ (M₂ : ℝ) * (γ * γ') ^ Kbig := mul_le_mul_of_nonneg_right hnondeg (le_of_lt hx)
    have hγ'1 : γ' ≤ 1 := by
      have h1 : Cbig * γ' ≤ 1 := le_trans hCγ' (by
        calc γ ^ Kbig ≤ γ ^ 1 := pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 (by omega)
          _ = γ := pow_one γ
          _ ≤ 1 := hγ1)
      nlinarith [hγ'0, h1, hCbig2]
    have hL1 : 1 ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) :=
      L_ge_one hγ0 hγ1 hγ'0 hCbig2 (by omega) (by exact_mod_cast hM₂pos) (by exact_mod_cast hM₂M₁)
        hCγ' hnondeg'
    have hgood := hGgood q hq
    have hgood' : γ / ((((m * (Fintype.card (Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1) * 2) ≤
        (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
          ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
            boxNorm (Fintype.card (FamIdx kω))
              (fun j => pDirFam p M₁ q.1 (Function.update q.2 s₀ a₀)
                ((Fintype.equivFin (FamIdx kω)).symm j))
              (symIcc (((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))) (f q.1) := by
      have hconv : γ / ((((m * (Fintype.card (Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1) * 2)
          = γ₁ / 2 := by rw [hγ₁, div_div]
      rw [hconv]
      exact hgood
    exact midPerQ k kω p D s₀ m hm hs1 tbig s' hs' C' A hC' hA Khc hKhc ht htm hconc
      Kbig Cbig c₁ Kh hKhc_le hKbig hCbig hc₁ hCbig2 M₁ M₂ N γ γ' q.1 q.2 (f q.1)
      hM₂pos hM₂M₁ hN hM₁₂ hγ0 hγ1 hγ'0 hCγ' hnondeg (hppos s₀.1 q.1 hqA)
      (hpshift s₀.1 q.1 hqA) (fun i => hDpshift i q.1 hqA) (hfsupp q.1 hqA) (hfb q.1 hqA) hqR
      (hδ₀ge γ hγ0) hL1 hgood' b₀

theorem mainBranch {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ) (s₀ : Slot ι k)
    (m : ℕ) (hm : Fintype.card (FamIdx kω) = m)
    (hs1 : 1 ≤ Fintype.card (AIdx k kω s₀))
    (tbig : ℕ) (s' : ℕ) (hs' : 1 ≤ s') (C' A : ℝ) (hC' : 0 < C') (hA : 1 ≤ A)
    (Khc : ℕ) (hKhc : 1 ≤ Khc) (ht : s' + 1 ≤ tbig) (htm : m ≤ tbig)
    (hconc : ∀ (c : ℤ), 0 < c → ∀ (Nw M₁ M₂ : ℕ) (d : Fin (Fintype.card (AIdx k kω s₀)) → ℤ)
        (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ Nw → (M₁ : ℝ) * (M₂ : ℝ) ≤ (Nw : ℝ) / (c : ℝ) →
        (∀ i : Fin (Fintype.card (AIdx k kω s₀)),
            |d i| ≤ (((Fintype.card (Slot ι k)) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ)) →
        SupportIn f Nw → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ Khc → A ≤ (M₂ : ℝ) * (δ * δ') ^ Khc →
        δ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
              ∑ a ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
                boxNorm (Fintype.card (AIdx k kω s₀))
                  (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
                    arithIcc (c * a + d i) M₁) (symIcc Nw) f →
        C' * (δ * δ') ^ Khc ≤
          uNorm s' (arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc Nw) f)
    (Kbig : ℕ) (Cbig : ℝ) (c₁ : ℝ) (Kh : ℕ) (hKhc_le : Khc ≤ Kh)
    (hKbig : 2 ^ (m + 1) * Kh + 1 ≤ Kbig) (hCbig : A / c₁ ^ Khc ≤ Cbig) (hc₁ : 0 < c₁)
    (hCbig2 : 2 ≤ Cbig)
    (hδ₀ge : ∀ γ : ℝ, 0 < γ → c₁ * γ ^ (2 ^ m) ≤
      ((γ / ((((m * (Fintype.card (Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1)) / 2) ^ (2 ^ m) / 2))
    (hKexp1 : 1 + (2 : ℝ) ^ m * (1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) /
        (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)) ≤ (Kbig : ℝ))
    (hKexp2 : (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)) ≤
        (Kbig : ℝ)) :
    ∃ cc : ℝ, 0 < cc ∧ ∀ (Adata : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ)
      (f : (Fin n → ℤ) → ℤ → ℂ),
      1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
      0 < γ → γ ≤ 1 → 0 < γ' → Cbig * γ' ≤ γ ^ Kbig →
      (∀ i a, a ∈ Adata → 0 < p i a) →
      (∀ i a, a ∈ Adata → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
      (∀ i a, a ∈ Adata → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
      (∀ a ∈ Adata, ∀ x : ℤ, ‖f a x‖ ≤ 1) → (∀ a ∈ Adata, SupportIn (f a) N) →
      Cbig * (γ * γ') ^ (-(Kbig : ℤ)) ≤ (M₂ : ℝ) →
      γ ≤ ((Adata.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
            ∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
              boxNorm (Fintype.card (FamIdx kω))
                (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a) →
      cc * (γ * γ') ^ Kbig ≤ ((Adata.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
            ∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂,
              boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
                (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
                  ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) (f a) := by
  classical
  set lev : ℕ := Fintype.card (ConclIdx s₀ kω tbig) with hlev
  set Kb : ℕ := m * (Fintype.card (Slot ι k) * D + 1) + 1 with hKbdef
  set e1 : ℝ := (1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev with he1
  set e2 : ℝ := (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev with he2
  set e3 : ℝ := (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev with he3
  set CC : ℝ := (1 / (2 * ((Kb : ℝ) + 1))) * c₁ ^ e1 * ((1 : ℝ) / 2) ^ (2 ^ tbig) *
      (C') ^ e2 with hCC
  have hbook1 : 1 + (2 : ℝ) ^ m * (1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev ≤
      (Kbig : ℝ) := by rw [hlev]; exact hKexp1
  have hbook2 : (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev ≤ (Kbig : ℝ) := by
    rw [hlev]; exact hKexp2
  have hCCpos : 0 < CC := by
    rw [hCC]
    have h1 : (0 : ℝ) < c₁ ^ e1 := Real.rpow_pos_of_pos hc₁ _
    have h2 : (0 : ℝ) < (C') ^ e2 := Real.rpow_pos_of_pos hC' _
    positivity
  refine ⟨CC, hCCpos, ?_⟩
  intro Adata M₁ M₂ N γ γ' f hM₂pos hM₂M₁ hN hM₁₂ hγ0 hγ1 hγ'0 hCγ' hppos hpshift hDpshift hfb
    hfsupp hnondeg hhyp
  set BB : ℝ := (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ lev) * ((1 : ℝ) / 2) ^ (2 ^ tbig) *
      (C') ^ e2 * (c₁ * γ ^ (2 ^ m) * γ') ^ e3 with hBB
  have hAd : Adata.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have h1 : γ ≤ 0 := by
      have h := hhyp
      rw [hzero] at h
      simp at h
      linarith
    linarith
  obtain ⟨G, hGsub, hGdens, hGpt⟩ := midBound k kω p D s₀ m hm hs1 tbig s' hs' C' A hC' hA Khc hKhc
    ht htm hconc Kbig Cbig c₁ Kh hKhc_le hKbig hCbig hc₁ hCbig2 hδ₀ge Adata M₁ M₂ N γ γ' f
    hM₂pos hM₂M₁ hN hM₁₂ hγ0 hγ1 hγ'0 hCγ' hAd hppos hpshift hDpshift hfb hfsupp hnondeg hhyp
  have hBB0 : 0 ≤ BB := by
    rw [hBB]
    have h1 : (0 : ℝ) < (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ lev) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h2 : (0 : ℝ) < (C') ^ e2 := Real.rpow_pos_of_pos hC' _
    have h3 : (0 : ℝ) < (c₁ * γ ^ (2 ^ m) * γ') ^ e3 := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hcv := concl_avg_sum k kω p D s₀ tbig Adata M₁ M₂ N γ' BB f hBB0 hM₂pos G hGsub
    (fun q hq b₀ hb₀ => by
      rw [hBB]
      exact hGpt q hq b₀ hb₀)
  have hconv : γ / (2 * ((Kb : ℝ) + 1)) =
      γ / (2 * ((((m * (Fintype.card (Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1))) := by
    rw [hKbdef]
  have hgb : γ / (2 * ((Kb : ℝ) + 1)) ≤
      (G.card : ℝ) / ((Adata.card : ℝ) *
        (((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)) := by
    rw [hconv]
    convert hGdens using 2
    ring
  have hcombine : (γ / (2 * ((Kb : ℝ) + 1))) * BB ≤
      ((Adata.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂,
          boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
            (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
              ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) (f a) := by
    calc (γ / (2 * ((Kb : ℝ) + 1))) * BB
        ≤ ((G.card : ℝ) / ((Adata.card : ℝ) *
            (((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ))) * BB :=
          mul_le_mul_of_nonneg_right hgb hBB0
      _ = ((Adata.card : ℝ))⁻¹ *
          (((paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
          (G.card : ℝ) * BB := by ring
      _ ≤ _ := hcv
  have hγ'1 : γ' ≤ 1 := by
    have h1 : Cbig * γ' ≤ 1 := le_trans hCγ' (by
      calc γ ^ Kbig ≤ γ ^ 1 := pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 (by omega)
        _ = γ := pow_one γ
        _ ≤ 1 := hγ1)
    nlinarith [hγ'0, h1, hCbig2]
  refine le_trans ?_ hcombine
  rw [hCC, hBB, he1, he2, he3]
  exact mainBookkeep hγ0 hγ1 hγ'0 hγ'1 hc₁ hC' hbook1 hbook2

end
end Work.Peluse.LadderA

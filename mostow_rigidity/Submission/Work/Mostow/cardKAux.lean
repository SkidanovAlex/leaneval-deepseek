import Mathlib
import Submission.Work.Mostow.gapAEvenDefs
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.bieberbachDefs
import Submission.Work.Mostow.jointEigenspacesCover
import Submission.Work.Mostow.dirichletBox

/-!
# Auxiliary lemmas for `cardK_strata`

Structural facts about `blk`/`resStd`/`nrmStd`, the elementary packing bound for finite subgroups
of a torus, and the abstract counting bound `|A| ≤ 2^s |ker σ|`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

lemma rotN_eq_mOf (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) : rotN R = mOf R := rfl

lemma rotN_refl (m : ℕ) : rotN (LinearIsometryEquiv.refl ℝ (E m)) = 0 := by
  have h : ((LinearIsometryEquiv.refl ℝ (E m)).toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      = ContinuousLinearMap.id ℝ (E m) := by ext x; simp
  rw [rotN, h, sub_self, norm_zero]

open Classical in
lemma resStd_blk (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (h : PO k 1) (R : E m ≃ₗᵢ[ℝ] E m) : resStd k m (blk k m h R) = h := by
  have hblk := blk_hom k m hAk hIk hA hI
  set hg : ∃ p : PO k 1 × (E m ≃ₗᵢ[ℝ] E m), blk k m h R = blk k m p.1 p.2 := ⟨(h, R), rfl⟩ with hgdef
  rw [resStd, dif_pos hg]
  exact ((hblk.2.2 h hg.choose.1 R hg.choose.2 (Classical.choose_spec hg)).1).symm

open Classical in
lemma nrmStd_blk (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (h : PO k 1) (R : E m ≃ₗᵢ[ℝ] E m) : nrmStd k m (blk k m h R) = R := by
  have hblk := blk_hom k m hAk hIk hA hI
  set hg : ∃ p : PO k 1 × (E m ≃ₗᵢ[ℝ] E m), blk k m h R = blk k m p.1 p.2 := ⟨(h, R), rfl⟩ with hgdef
  rw [nrmStd, dif_pos hg]
  exact ((hblk.2.2 h hg.choose.1 R hg.choose.2 (Classical.choose_spec hg)).2).symm

lemma resStd_one (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) :
    resStd k m (1 : PO (k + m) 1) = 1 := by
  have h := resStd_blk k m hAk hIk hA hI (1 : PO k 1) (1 : E m ≃ₗᵢ[ℝ] E m)
  rwa [(blk_hom k m hAk hIk hA hI).2.1] at h

lemma nrmStd_one (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) :
    nrmStd k m (1 : PO (k + m) 1) = 1 := by
  have h := nrmStd_blk k m hAk hIk hA hI (1 : PO k 1) (1 : E m ≃ₗᵢ[ℝ] E m)
  rwa [(blk_hom k m hAk hIk hA hI).2.1] at h

lemma eq_blk_resStd_nrmStd (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (c : PO (k + m) 1) (hc : ∃ p : PO k 1 × (E m ≃ₗᵢ[ℝ] E m), c = blk k m p.1 p.2) :
    c = blk k m (resStd k m c) (nrmStd k m c) := by
  obtain ⟨p, rfl⟩ := hc
  rw [resStd_blk k m hAk hIk hA hI p.1 p.2, nrmStd_blk k m hAk hIk hA hI p.1 p.2]

open Classical in
lemma block_of_hyp {m : ℕ} (j : ℕ) (θ_J θ : ℝ) (hθJ : 0 ≤ θ_J) (hθ0 : 0 < θ)
    {Λ : Subgroup (PO (j + m) 1)} {b c : PO (j + m) 1}
    (HYP : ∀ c : PO (j + m) 1, c ∈ Λ → c ∈ Subgroup.centralizer {b} → resStd j m c = 1 →
      c ≠ 1 → rotN (nrmStd j m c) ≤ θ_J → θ ≤ rotN (nrmStd j m c))
    (hcΛ : c ∈ Λ) (hcC : c ∈ Subgroup.centralizer {b}) (hcS : resStd j m c = 1)
    (hc1 : c ≠ 1) : ∃ p : PO j 1 × (E m ≃ₗᵢ[ℝ] E m), c = blk j m p.1 p.2 := by
  by_contra hcon
  have hnrm : nrmStd j m c = LinearIsometryEquiv.refl ℝ (E m) := by
    rw [nrmStd]; exact dif_neg hcon
  have hle : rotN (nrmStd j m c) ≤ θ_J := by
    rw [hnrm, rotN_refl m]; exact hθJ
  have h := HYP c hcΛ hcC hcS hc1 hle
  rw [hnrm, rotN_refl m] at h
  linarith

lemma closure_commutative {G : Type*} [Group G] {S : Set G}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
  have h1 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    have hsub : Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.closure_le]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (hS z hz y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp (hsub hx) y (Set.mem_singleton y)).symm
  intro a ha b hb
  have hsub : Subgroup.closure S ≤ Subgroup.centralizer ((Subgroup.closure S : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr (fun w hw => h1 w hw z hz)
  exact (Subgroup.mem_centralizer_iff.mp (hsub ha) b hb).symm

open Classical in
lemma torusSubgroupCard (r : ℕ) (Λ : AddSubgroup (Fin r → AddCircle (2 * Real.pi))) [Finite Λ]
    (v : ℝ) (hv : 0 < v) (hsep : ∀ a ∈ Λ, a ≠ 0 → ∃ i, v ≤ ‖a i‖) :
    (Nat.card Λ : ℝ) ≤ (1 + 4 * Real.pi / v) ^ r := by
  set α : Fin r → ℝ := fun _ => v / 2 with hαdef
  have hαpos : ∀ i, 0 < α i := fun i => by rw [hαdef]; positivity
  set c : ℕ := ⌈4 * Real.pi / v⌉₊ with hcdef
  have hci : ∀ i : Fin r, ⌈2 * Real.pi / α i⌉₊ = c := by
    intro i
    rw [hcdef, hαdef]
    congr 1
    field_simp
    ring
  let box : Λ → ((i : Fin r) → Fin ⌈2 * Real.pi / α i⌉₊) :=
    fun a i => boxIdx α hαpos i ((a : Fin r → AddCircle (2 * Real.pi)) i)
  have hinj : Function.Injective box := by
    intro a b hab
    by_contra hne
    have hcoord : ∀ i,
        ‖(a : Fin r → AddCircle (2 * Real.pi)) i - (b : Fin r → AddCircle (2 * Real.pi)) i‖ < α i := by
      intro i
      exact boxIdx_eq_imp α hαpos i (congrFun hab i)
    have hmem : (a : Fin r → AddCircle (2 * Real.pi)) - b ∈ Λ := sub_mem a.2 b.2
    have hne0 : (a : Fin r → AddCircle (2 * Real.pi)) - b ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
    obtain ⟨i, hi⟩ := hsep _ hmem hne0
    have h2 := hcoord i
    rw [hαdef] at h2
    simp only [Pi.sub_apply] at hi h2
    linarith
  have hcard : Nat.card Λ ≤ c ^ r := by
    haveI : Fintype ↥Λ := Fintype.ofFinite _
    have h1 : Fintype.card ↥Λ ≤ Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / α i⌉₊) :=
      Fintype.card_le_of_injective box hinj
    rw [Nat.card_eq_fintype_card]
    refine le_trans h1 (le_of_eq ?_)
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_congr rfl (fun i _ => hci i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hcv : (c : ℝ) ≤ 1 + 4 * Real.pi / v := by
    have h1 : (c : ℝ) < 4 * Real.pi / v + 1 := by
      rw [hcdef]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  calc (Nat.card Λ : ℝ) ≤ (c : ℝ) ^ r := by exact_mod_cast hcard
    _ ≤ (1 + 4 * Real.pi / v) ^ r := pow_le_pow_left₀ (by positivity) hcv r

open Classical in
lemma card_le_sign_mul_kernel {A : Type*} [Group A] [Finite A] {s : ℕ}
    (σ : A → (Fin s → ZMod 2)) (hσ1 : σ 1 = 0)
    (hadd : ∀ a b : A, σ (a * b) = σ a + σ b)
    (A₀ : Subgroup A) (hA₀ : ∀ a : A, a ∈ A₀ ↔ σ a = 0) :
    Nat.card A ≤ 2 ^ s * Nat.card ↥A₀ := by
  haveI : Fintype A := Fintype.ofFinite A
  have hsub : ∀ a : A, σ (a⁻¹) = - σ a := by
    intro a
    have h : σ a + σ a⁻¹ = 0 := by rw [← hadd, mul_inv_cancel, hσ1]
    simpa using eq_neg_of_add_eq_zero_right h
  have hfiber : ∀ y : (Fin s → ZMod 2), Nat.card {a : A // σ a = y} ≤ Nat.card ↥A₀ := by
    intro y
    by_cases hy : ∃ a : A, σ a = y
    · obtain ⟨a₀, ha₀⟩ := hy
      have hinj : Function.Injective (fun p : {a : A // σ a = y} =>
          (⟨(p.1 : A) * a₀⁻¹, by
            rw [hA₀, hadd, hsub, p.2, ha₀]
            simp⟩ : ↥A₀)) := by
        intro p q hpq
        have h1 : (p.1 : A) * a₀⁻¹ = (q.1 : A) * a₀⁻¹ := congrArg Subtype.val hpq
        exact Subtype.ext (mul_right_cancel h1)
      exact Nat.card_le_card_of_injective _ hinj
    · push_neg at hy
      have hempty : IsEmpty {a : A // σ a = y} := ⟨fun p => hy p.1 p.2⟩
      rw [Nat.card_eq_zero.mpr (Or.inl hempty)]
      exact Nat.zero_le _
  have hsum : Nat.card A = ∑ y : (Fin s → ZMod 2), Nat.card {a : A // σ a = y} := by
    have heq : A ≃ (Σ y : (Fin s → ZMod 2), {a : A // σ a = y}) :=
      { toFun := fun a => ⟨σ a, ⟨a, rfl⟩⟩
        invFun := fun p => p.2.1
        left_inv := fun a => rfl
        right_inv := fun p => by
          obtain ⟨y, a, ha⟩ := p
          subst ha
          rfl }
    rw [Nat.card_congr heq, Nat.card_sigma]
  calc Nat.card A = ∑ y : (Fin s → ZMod 2), Nat.card {a : A // σ a = y} := hsum
    _ ≤ ∑ y : (Fin s → ZMod 2), Nat.card ↥A₀ := Finset.sum_le_sum (fun y _ => hfiber y)
    _ = 2 ^ s * Nat.card ↥A₀ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        simp [nsmul_eq_mul]


open Classical in
lemma nat_card_le_sum_fibers {α β : Type*} [Finite α] [Fintype β] (f : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // f a = b} := by
  have heq : α ≃ (Σ b : β, {a : α // f a = b}) :=
    { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun a => rfl
      right_inv := fun p => by
        obtain ⟨b, a, ha⟩ := p
        subst ha
        rfl }
  rw [Nat.card_congr heq, Nat.card_sigma]

open Classical in
/-- The conclusion form of `orthTorusData`, packaged as an assumption. -/
def OrthTorusForm (m : ℕ) : Prop :=
  ∀ (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite A], (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    ∃ (r s : ℕ) (hrs : 2 * r + s ≤ m)
      (ψ : A → (Fin r → AddCircle (2 * Real.pi))) (σ : A → (Fin s → ZMod 2)),
      ψ 1 = 0 ∧ σ 1 = 0 ∧
      (∀ a b : A, ψ (a * b) = ψ a + ψ b ∧ σ (a * b) = σ a + σ b) ∧
      (∀ a : A, ψ a = 0 → σ a = 0 → a = 1) ∧
      (∀ a : A, mOf (a : E m ≃ₗᵢ[ℝ] E m) ≤
        (∑ i : Fin r, ‖ψ a i‖) + (if σ a = 0 then 0 else 2))

open Classical in
lemma abelianCard_of (m : ℕ) (H : OrthTorusForm m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite A],
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → ∀ v : ℝ, 0 < v →
      (∀ a ∈ A, a ≠ 1 → v ≤ mOf a) → (Nat.card A : ℝ) ≤ K * (1 + v ^ (-(m : ℝ) / 2)) := by
  refine ⟨(2 : ℝ) ^ (m + 1) * (1 + 4 * Real.pi * (m : ℝ)) ^ m, by positivity, ?_⟩
  intro A hAfin hcomm v hv hsep
  obtain ⟨r, s, hrs, ψ, σ, hψ1, hσ1, hadd, hsep0, hnorm⟩ := H A hcomm
  have hψmul : ∀ a b : A, ψ (a * b) = ψ a + ψ b := fun a b => (hadd a b).1
  have hσmul : ∀ a b : A, σ (a * b) = σ a + σ b := fun a b => (hadd a b).2
  have hψinv : ∀ a : A, ψ (a⁻¹) = - ψ a := by
    intro a
    have h : ψ a + ψ a⁻¹ = 0 := by rw [← hψmul, mul_inv_cancel, hψ1]
    simpa using eq_neg_of_add_eq_zero_right h
  let A₀ : Subgroup A :=
    { carrier := {a : A | σ a = 0}
      mul_mem' := by
        intro a b ha hb
        show σ (a * b) = 0
        rw [hσmul, ha, hb, add_zero]
      one_mem' := hσ1
      inv_mem' := by
        intro a ha
        show σ a⁻¹ = 0
        have h : σ a⁻¹ = - σ a := by
          have h2 : σ a + σ a⁻¹ = 0 := by rw [← hσmul, mul_inv_cancel, hσ1]
          simpa using eq_neg_of_add_eq_zero_right h2
        rw [h, ha, neg_zero] }
  have hsign : Nat.card A ≤ 2 ^ s * Nat.card ↥A₀ :=
    card_le_sign_mul_kernel σ hσ1 hσmul A₀ (fun a => Iff.rfl)
  let L : AddSubgroup (Fin r → AddCircle (2 * Real.pi)) :=
    { carrier := ψ '' (A₀ : Set A)
      add_mem' := by
        intro x y hx hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a * b, A₀.mul_mem ha hb, hψmul a b⟩
      zero_mem' := ⟨1, A₀.one_mem, hψ1⟩
      neg_mem' := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨a⁻¹, A₀.inv_mem ha, hψinv a⟩ }
  have hsurj : Function.Surjective (fun a : A₀ => (⟨ψ (a : A), ⟨a, a.2, rfl⟩⟩ : ↥L)) := by
    intro z
    obtain ⟨a, ha, haz⟩ := z.2
    exact ⟨⟨a, ha⟩, Subtype.ext haz⟩
  haveI : Finite ↥L :=
    Finite.of_surjective (fun a : A₀ => (⟨ψ (a : A), ⟨a, a.2, rfl⟩⟩ : ↥L)) hsurj
  have hkey : ∀ a b : A₀, ψ (a : A) = ψ (b : A) → a = b := by
    intro a b h1
    have hσa : σ (a : A) = 0 := a.2
    have hσb : σ (b : A) = 0 := b.2
    have h2 : ψ ((a : A) * (b : A)⁻¹) = 0 := by
      rw [hψmul, hψinv, h1]
      simp
    have hσb' : σ (b : A)⁻¹ = - σ (b : A) := by
      have h2' : σ (b : A) + σ (b : A)⁻¹ = 0 := by rw [← hσmul, mul_inv_cancel, hσ1]
      simpa using eq_neg_of_add_eq_zero_right h2'
    have h3 : σ ((a : A) * (b : A)⁻¹) = 0 := by
      rw [hσmul, hσb', hσa, hσb]
      simp
    have h4 : (a : A) * (b : A)⁻¹ = 1 := hsep0 _ h2 h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  have hLcard : Nat.card ↥L = Nat.card ↥A₀ := by
    have h2 : Nat.card ↥L ≤ Nat.card ↥A₀ :=
      Nat.card_le_card_of_surjective (fun a : A₀ => (⟨ψ (a : A), ⟨a, a.2, rfl⟩⟩ : ↥L)) hsurj
    have h1 : Nat.card ↥A₀ ≤ Nat.card ↥L :=
      Nat.card_le_card_of_injective (fun a : A₀ => (⟨ψ (a : A), ⟨a, a.2, rfl⟩⟩ : ↥L))
        (fun a b hab => hkey a b (congrArg Subtype.val hab))
    exact le_antisymm h2 h1
  set w : ℝ := if r = 0 then 1 else v / r with hwdef
  have hwpos : 0 < w := by
    by_cases hr0 : r = 0
    · rw [hwdef, if_pos hr0]; norm_num
    · rw [hwdef, if_neg hr0]; positivity
  have hsepL : ∀ x ∈ L, x ≠ 0 → ∃ i : Fin r, w ≤ ‖x i‖ := by
    intro x hx hx0
    obtain ⟨a, ha, rfl⟩ := hx
    have hψne : ψ (a : A) ≠ 0 := hx0
    have ha1 : ((a : A) : E m ≃ₗᵢ[ℝ] E m) ≠ 1 := by
      intro h
      exact hψne (by rw [show (a : A) = 1 from Subtype.ext h, hψ1])
    by_cases hr0 : r = 0
    · exfalso
      have hz : ψ (a : A) = 0 := by
        funext i
        exact absurd (lt_of_lt_of_eq i.2 hr0) (Nat.not_lt_zero _)
      exact hψne hz
    · have hwv : w = v / r := by rw [hwdef, if_neg hr0]
      rw [hwv]
      have hσa : σ (a : A) = 0 := ha
      have hsub : v ≤ ∑ i : Fin r, ‖ψ (a : A) i‖ := by
        have h := hnorm (a : A)
        rw [if_pos hσa] at h
        exact le_trans (hsep ((a : A) : E m ≃ₗᵢ[ℝ] E m) (a : A).2 ha1) (by simpa using h)
      by_contra hcon
      push_neg at hcon
      have hlt : (∑ i : Fin r, ‖ψ (a : A) i‖) < v := by
        calc (∑ i : Fin r, ‖ψ (a : A) i‖) < ∑ _i : Fin r, (v / r) := by
              apply Finset.sum_lt_sum_of_nonempty
              · exact ⟨⟨0, Nat.pos_of_ne_zero hr0⟩, Finset.mem_univ _⟩
              · intro i _
                exact hcon i
          _ = v := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
      linarith
  have hLreal : (Nat.card ↥L : ℝ) ≤ (1 + 4 * Real.pi / w) ^ r :=
    torusSubgroupCard r L w hwpos hsepL
  have hA₀real : (Nat.card ↥A₀ : ℝ) ≤ (1 + 4 * Real.pi * (r : ℝ) / v) ^ r := by
    rw [← hLcard]
    refine le_trans hLreal ?_
    by_cases hr0 : r = 0
    · rw [hr0]; simp
    · have hwv : w = v / r := by rw [hwdef, if_neg hr0]
      have hbase : 1 + 4 * Real.pi / w = 1 + 4 * Real.pi * (r : ℝ) / v := by
        rw [hwv]
        field_simp
      rw [hbase]
  have hnat : Nat.card A ≤ 2 ^ s * ⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ := by
    refine le_trans hsign (Nat.mul_le_mul_left _ ?_)
    have h1 : ((Nat.card ↥A₀ : ℕ) : ℝ)
        ≤ ((⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ) :=
      le_trans hA₀real (Nat.le_ceil _)
    exact Nat.cast_le.mp h1
  have hceil : ((⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ)
      ≤ 2 * ((1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2)) := by
    have h1 : ((⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ)
        ≤ (1 + 4 * Real.pi * (r : ℝ) / v) ^ r + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h2 : (1 + 4 * Real.pi * (r : ℝ) / v) ^ r + 1
        ≤ 2 * ((1 + 4 * Real.pi * (r : ℝ) / v) ^ r) := by
      have h3 : (1 : ℝ) ≤ (1 + 4 * Real.pi * (r : ℝ) / v) ^ r := by
        refine one_le_pow₀ ?_
        have h0 : (0:ℝ) ≤ 4 * Real.pi * (r : ℝ) / v := by positivity
        linarith
      linarith
    have hr2 : (r : ℝ) ≤ (m : ℝ) / 2 := by
      have h2r : (2 * r : ℕ) ≤ m := by omega
      have : (2 * (r : ℝ)) ≤ (m : ℝ) := by exact_mod_cast h2r
      linarith
    have h3 : (1 + 4 * Real.pi * (r : ℝ) / v) ^ r
        ≤ (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2) := by
      have hrle : (r : ℝ) ≤ (m : ℝ) := by
        have : r ≤ m := by omega
        exact_mod_cast this
      have hbase : (1 + 4 * Real.pi * (r : ℝ) / v) ≤ (1 + 4 * Real.pi * (m : ℝ) / v) := by
        have h4 : 4 * Real.pi * (r : ℝ) / v ≤ 4 * Real.pi * (m : ℝ) / v := by
          apply div_le_div_of_nonneg_right _ hv.le
          nlinarith [Real.pi_pos, hrle]
        linarith
      refine le_trans (pow_le_pow_left₀ (by positivity) hbase r) ?_
      have h5 : (1 : ℝ) ≤ 1 + 4 * Real.pi * (m : ℝ) / v := by
        have h0 : (0:ℝ) ≤ 4 * Real.pi * (m : ℝ) / v := by positivity
        linarith
      calc (1 + 4 * Real.pi * (m : ℝ) / v) ^ r
          = (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((r : ℝ)) := (Real.rpow_natCast _ r).symm
        _ ≤ (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le h5 hr2
    linarith
  have hA1 : (1 : ℝ) ≤ 1 + 4 * Real.pi * (m : ℝ) := by
    have h0 : (0 : ℝ) ≤ 4 * Real.pi * (m : ℝ) := by positivity
    linarith
  have hexp_le : (m : ℝ) / 2 ≤ (m : ℝ) := by
    have hmn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hA0r : (1 + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2)
      ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hA1 hexp_le
  have hA0mono : (1 + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ)) = (1 + 4 * Real.pi * (m : ℝ)) ^ m :=
    Real.rpow_natCast _ m
  have hT : (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2)
      ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m * (1 + v ^ (-(m : ℝ) / 2)) := by
    by_cases hv1 : v ≤ 1
    · have hC : (1 + 4 * Real.pi * (m : ℝ) / v) = (v + 4 * Real.pi * (m : ℝ)) / v := by
        field_simp
      have hT' : (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2)
          = (v + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2) * v ^ (-(m : ℝ) / 2) := by
        rw [hC, Real.div_rpow (by positivity) hv.le, div_eq_mul_inv,
          ← Real.rpow_neg hv.le ((m : ℝ) / 2)]
        have hthis : -((m : ℝ) / 2) = (-(m : ℝ)) / 2 := by ring
        rw [hthis]
      rw [hT']
      have hb : (v + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2)
          ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      have hbd : (1 + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2)
          ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m := by
        rw [← hA0mono]; exact hA0r
      have hvnn : 0 ≤ v ^ (-(m : ℝ) / 2) := Real.rpow_nonneg hv.le _
      calc (v + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2) * v ^ (-(m : ℝ) / 2)
          ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m * v ^ (-(m : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (le_trans hb hbd) hvnn
        _ ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m * (1 + v ^ (-(m : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
    · push_neg at hv1
      have hC : (1 + 4 * Real.pi * (m : ℝ) / v) ≤ 1 + 4 * Real.pi * (m : ℝ) := by
        have h4 : 4 * Real.pi * (m : ℝ) / v ≤ 4 * Real.pi * (m : ℝ) := by
          rw [div_le_iff₀ hv]
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith [Real.pi_pos, hv1.le, hm0]
        linarith
      have h1 : (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2)
          ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ ((m : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hC (by positivity)
      have h2 : (1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2)
          ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m := by
        rw [← hA0mono]; exact le_trans h1 hA0r
      have h3 : (0 : ℝ) ≤ v ^ (-(m : ℝ) / 2) := Real.rpow_nonneg hv.le _
      have h4 : (0 : ℝ) ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m := by positivity
      have h5 : (1 + 4 * Real.pi * (m : ℝ)) ^ m
          ≤ (1 + 4 * Real.pi * (m : ℝ)) ^ m * (1 + v ^ (-(m : ℝ) / 2)) := by
        nlinarith [h3, h4]
      exact le_trans h2 h5
  have hfinal : (Nat.card A : ℝ)
      ≤ (2 : ℝ) ^ (m + 1) * (1 + 4 * Real.pi * (m : ℝ)) ^ m * (1 + v ^ (-(m : ℝ) / 2)) := by
    have h1 : (Nat.card A : ℝ) ≤ ((2 ^ s * ⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have h2 : ((2 ^ s * ⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ)
        = (2 : ℝ) ^ s * ((⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ) := by
      push_cast; ring
    have hsle : s ≤ m := by omega
    have h3 : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hsle
    calc (Nat.card A : ℝ)
        ≤ (2 : ℝ) ^ s * ((⌈(1 + 4 * Real.pi * (r : ℝ) / v) ^ r⌉₊ : ℕ) : ℝ) := by
          rw [← h2]; exact h1
      _ ≤ (2 : ℝ) ^ m * (2 * ((1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2))) := by
          gcongr
      _ = (2 : ℝ) ^ (m + 1) * ((1 + 4 * Real.pi * (m : ℝ) / v) ^ ((m : ℝ) / 2)) := by
          ring
      _ ≤ (2 : ℝ) ^ (m + 1)
            * ((1 + 4 * Real.pi * (m : ℝ)) ^ m * (1 + v ^ (-(m : ℝ) / 2))) := by
          exact mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (2 : ℝ) ^ (m + 1) * (1 + 4 * Real.pi * (m : ℝ)) ^ m * (1 + v ^ (-(m : ℝ) / 2)) := by
          ring
  exact hfinal


end

end Work.Mostow

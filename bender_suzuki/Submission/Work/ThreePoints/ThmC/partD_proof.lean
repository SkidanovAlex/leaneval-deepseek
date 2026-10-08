import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.Prop2h2t
import Submission.Work.ThreePoints.ThmC.even_card_of_twoTransitive
import Submission.Work.ThreePoints.ThmC.mem_centralizer_of_sq_mem_centralizer
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ThreePoints.ThmC

/-- If `K` is normal in `H ⊔ K` and `x ∈ H ⊔ K`, then `x = h * k` with `h ∈ H`, `k ∈ K`. -/
theorem exists_mul_mem_of_mem_sup {G : Type} [Group G] {H K : Subgroup G}
    (hK : ∀ x ∈ H ⊔ K, ∀ k ∈ K, x * k * x⁻¹ ∈ K) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (k := (H : Set G) ∪ (K : Set G))
    (p := fun x _ => ∃ h ∈ H, ∃ k ∈ K, h * k = x) ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, y, hy, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · rintro x y _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, h₂⁻¹ * k₁ * h₂ * k₂, ?_, by group⟩
    exact K.mul_mem (by simpa using hK h₂⁻¹ (Subgroup.mem_sup_left (H.inv_mem hh₂)) k₁ hk₁) hk₂
  · rintro x _ ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, h * k⁻¹ * h⁻¹, ?_, by group⟩
    exact hK h (Subgroup.mem_sup_left hh) k⁻¹ (K.inv_mem hk)

/-- **Peterfalvi I Ch. II §2 Lemma 1 (d) (p. 164).** -/
theorem partD_proof {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hA : Work.ThreePoints.ThmC.IsMaxP3 H p P)
    (hB : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G)))) :
    ¬ Work.ThreePoints.ThmC.IsSylowOf p P
        (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g)) →
      ∀ x ∈ P, u * x = x * u := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hnot
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let M : Subgroup G := Subgroup.normalizer (P : Set G)
  let X : Subgroup G := P ⊔ C
  -- ## elementary facts about `P`
  have hPp : IsPGroup p P := hP.2.1
  have hPd : P ≤ Submission.Blueprint.twoPoint H g := hP.1.trans inf_le_left
  have hPH : P ≤ H := hPd.trans inf_le_left
  have hPHg : P ≤ Submission.Blueprint.conj g H := hPd.trans inf_le_right
  have huM : u ∈ M := huP
  have hu2 : orderOf u = 2 := hu.2
  have hPodd : Odd (Nat.card ↥P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    rw [hn]
    exact Odd.pow (Nat.Prime.odd_of_ne_two hp hpodd)
  have hXM : X ≤ M := sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  -- ## Step 1: a `p`-subgroup `Q` with `P < Q` inside `X ⊓ D`
  have hnot2 : ¬ (∀ Q : Subgroup G, P ≤ Q →
      Q ≤ P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g) →
      IsPGroup p Q → Q = P) := fun hc => hnot ⟨le_sup_left, hPp, hc⟩
  push_neg at hnot2
  obtain ⟨Q, hPQ, hQXd, hQp, hQne⟩ := hnot2
  have hQX : Q ≤ X := hQXd.trans (sup_le le_sup_left (le_trans inf_le_left le_sup_right))
  have hQD : Q ≤ Submission.Blueprint.twoPoint H g := hQXd.trans (sup_le hPd inf_le_right)
  have hQH : Q ≤ H := hQD.trans inf_le_left
  have hQHg : Q ≤ Submission.Blueprint.conj g H := hQD.trans inf_le_right
  have hPltQ : P < Q := lt_of_le_of_ne hPQ (Ne.symm hQne)
  -- ## Step 2: the fixed points of `Q` are exactly `{1, g}`
  have h1Q : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H Q :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact hQH)
  have hgQ : ((g : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H Q :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
      rw [Work.ThreePoints.stabilizer_mk]; exact hQHg)
  have h1g : ((1 : G) : G ⧸ H) ≠ ((g : G) : G ⧸ H) := by
    intro h
    rw [QuotientGroup.eq] at h
    exact hg (by simpa using h)
  have hsubQ : ({((1 : G) : G ⧸ H), ((g : G) : G ⧸ H)} : Set (G ⧸ H)) ⊆
      Submission.Blueprint.fixedPts H Q := by
    intro ω hω
    rcases hω with h | h
    · rw [h]; exact h1Q
    · rw [h]; exact hgQ
  have hQfixset : Submission.Blueprint.fixedPts H Q =
      ({((1 : G) : G ⧸ H), ((g : G) : G ⧸ H)} : Set (G ⧸ H)) := by
    have h2 : 2 ≤ (Submission.Blueprint.fixedPts H Q).ncard := by
      have h := Set.ncard_le_ncard hsubQ (Set.toFinite _)
      rwa [Set.ncard_pair h1g] at h
    have h3 : (Submission.Blueprint.fixedPts H Q).ncard ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      exact hQne (hA.2.2 Q hPQ hQp (by omega))
    exact (Set.eq_of_subset_of_ncard_le hsubQ (by rw [Set.ncard_pair h1g]; exact h3)).symm
  -- ## Step 3: `X` acts on `Ω_P`
  have h1P : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact hPH)
  have hgP : ((g : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by
      rw [Work.ThreePoints.stabilizer_mk]; exact hPHg)
  have hNsmul : ∀ m : G, m ∈ M → ∀ ω ∈ Submission.Blueprint.fixedPts H P,
      m • ω ∈ Submission.Blueprint.fixedPts H P := by
    intro m hm ω hω
    rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
    intro q hq
    have h1 : m⁻¹ * q * m ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (M.inv_mem hm) q).mp hq
    calc q • (m • ω) = (q * m) • ω := by rw [mul_smul]
      _ = (m * (m⁻¹ * q * m)) • ω := by rw [show q * m = m * (m⁻¹ * q * m) from by group]
      _ = m • ((m⁻¹ * q * m) • ω) := by rw [mul_smul]
      _ = m • ω := by rw [hω _ h1]
  let act : MulAction ↥X ↥(Submission.Blueprint.fixedPts H P) :=
    { smul := fun m ω => ⟨(m : G) • (ω : G ⧸ H),
        hNsmul (m : G) (hXM m.2) (ω : G ⧸ H) ω.2⟩
      one_smul := fun ω => Subtype.ext (one_smul G (ω : G ⧸ H))
      mul_smul := fun m₁ m₂ ω => Subtype.ext (by
        show ((m₁ * m₂ : ↥X) : G) • (ω : G ⧸ H) = (m₁ : G) • ((m₂ : G) • (ω : G ⧸ H))
        rw [Subgroup.coe_mul, mul_smul]) }
  letI := act
  -- ## Step 4: `X` is `2`-transitive on `Ω_P`
  have hleC : ∀ m ∈ M, Submission.Blueprint.conj m C ≤ C := by
    intro m hm
    rintro x hx
    rw [Work.ThreePoints.mem_conj_iff] at hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : m⁻¹ * y * m ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (M.inv_mem hm) y).mp hy
    have h := hx (m⁻¹ * y * m) hy'
    have h2 := congrArg (fun t => m * t * m⁻¹) h
    have e1 : m * ((m⁻¹ * y * m) * (m⁻¹ * x * m)) * m⁻¹ = y * x := by group
    have e2 : m * ((m⁻¹ * x * m) * (m⁻¹ * y * m)) * m⁻¹ = x * y := by group
    rwa [e1, e2] at h2
  have hconjC : ∀ m ∈ M, Submission.Blueprint.conj m C = C := by
    intro m hm
    refine le_antisymm (hleC m hm) ?_
    have h2 : Submission.Blueprint.conj m (Submission.Blueprint.conj m⁻¹ C) ≤
        Submission.Blueprint.conj m C := Subgroup.map_mono (hleC m⁻¹ (M.inv_mem hm))
    rwa [← Work.ThreePoints.conj_mul, mul_inv_cancel, Work.ThreePoints.conj_one] at h2
  have hconjX : ∀ m ∈ M, Submission.Blueprint.conj m X = X := by
    intro m hm
    have hmP : Submission.Blueprint.conj m P = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hm
    show Subgroup.map (MulAut.conj m).toMonoidHom (P ⊔ C) = P ⊔ C
    have h1 : Subgroup.map (MulAut.conj m).toMonoidHom P = P := hmP
    have h2 : Subgroup.map (MulAut.conj m).toMonoidHom C = C := hconjC m hm
    rw [Subgroup.map_sup, h1, h2]
  have hmem_fb : ∀ (R : Subgroup G) (hRX : R ≤ X)
      (ω : ↥(Submission.Blueprint.fixedPts H P)),
      ω ∈ Work.DoubleTransitivity.fixedBySub (R.subgroupOf X) ↔
        (ω : G ⧸ H) ∈ Submission.Blueprint.fixedPts H R := by
    intro R hRX ω
    rw [Work.DoubleTransitivity.mem_fixedBySub, Work.ThreePoints.mem_fixedPts]
    constructor
    · intro h r hr
      have hh := h ⟨r, hRX hr⟩ (Subgroup.mem_subgroupOf.mpr hr)
      exact Subtype.ext_iff.mp hh
    · intro h r hr
      exact Subtype.ext (h (r : G) (Subgroup.mem_subgroupOf.mp hr))
  haveI : Fintype ↥(Submission.Blueprint.fixedPts H P) := Fintype.ofFinite _
  have h2tX : MulAction.IsMultiplyPretransitive ↥X
      ↥(Submission.Blueprint.fixedPts H P) 2 := by
    refine Work.DoubleTransitivity.App2.app2_4 (p := p) ?_ ?_
    · rw [Set.ncard_univ, Nat.card_coe_set_eq]
      exact hA.2.1
    · intro a b hab
      obtain ⟨m, hmM, hm1, hmg⟩ := hB.1 (((1 : G)) : G ⧸ H) h1P (((g : G)) : G ⧸ H) hgP h1g
        (a : G ⧸ H) a.2 (b : G ⧸ H) b.2 (fun h => hab (Subtype.ext h))
      have hQX' : Submission.Blueprint.conj m Q ≤ X := by
        rw [← hconjX m hmM]
        exact Subgroup.map_mono hQX
      refine ⟨(Submission.Blueprint.conj m Q).subgroupOf X, ?_, ?_⟩
      · exact (hQp.map (MulAut.conj m).toMonoidHom).comap_of_injective X.subtype
          Subtype.coe_injective
      · ext ω
        rw [hmem_fb (Submission.Blueprint.conj m Q) hQX' ω]
        rw [Work.ThreePoints.fixedPts_conj H m Q, Set.mem_smul_set_iff_inv_smul_mem]
        constructor
        · intro hω
          have hω' : m⁻¹ • (ω : G ⧸ H) ∈
              ({((1 : G) : G ⧸ H), ((g : G) : G ⧸ H)} : Set (G ⧸ H)) := by
            rw [← hQfixset]; exact hω
          rcases hω' with h1 | h1
          · left
            apply Subtype.ext
            show (ω : G ⧸ H) = (a : G ⧸ H)
            rw [← hm1, ← h1, smul_inv_smul]
          · right
            apply Subtype.ext
            show (ω : G ⧸ H) = (b : G ⧸ H)
            rw [← hmg, ← h1, smul_inv_smul]
        · intro hω
          rcases hω with h1 | h1
          · rw [h1]
            show m⁻¹ • (a : G ⧸ H) ∈ Submission.Blueprint.fixedPts H Q
            rw [← hm1, inv_smul_smul]
            exact h1Q
          · rw [h1]
            show m⁻¹ • (b : G ⧸ H) ∈ Submission.Blueprint.fixedPts H Q
            rw [← hmg, inv_smul_smul]
            exact hgQ
  -- ## Step 5: `|X|` is even
  have hXeven : Even (Nat.card ↥X) :=
    even_card_of_twoTransitive h2tX (by rw [Nat.card_coe_set_eq]; exact hA.2.1)
  obtain ⟨v, hvX, hv2⟩ : ∃ v : G, v ∈ X ∧ orderOf v = 2 := by
    haveI : Fintype ↥X := Fintype.ofFinite _
    have hdvd : 2 ∣ Fintype.card ↥X := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp hXeven
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card (G := ↥X) 2 hdvd
    exact ⟨(w : G), w.2, (Subgroup.orderOf_coe w).trans hw⟩
  -- ## Step 6: `u` is conjugate to `v` in `M`, hence `u ∈ X`
  have hvM : v ∈ M := hXM hvX
  have hMstrong : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((M ⊓ H).subgroupOf M) := by
    have h := hB.2 1 (by rw [Work.ThreePoints.conj_one]; exact hPH)
    rwa [Work.ThreePoints.conj_one] at h
  have hun : orderOf (⟨u, huM⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hvn : orderOf (⟨v, hvM⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hv2
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (Work.ThreePoints.involutions_conj_of_stronglyEmbedded hMstrong hun hvn)
  have hcG : (c : G) * u * (c : G)⁻¹ = v := by
    have := congrArg (fun y : ↥M => (y : G)) hc
    simpa using this
  have huX : u ∈ X := by
    have h2 : u = ((c : G))⁻¹ * v * ((c : G)) := by
      rw [← hcG]; group
    have hv : v ∈ Submission.Blueprint.conj (c : G) X := by
      rw [hconjX (c : G) c.2]; exact hvX
    have hvc : ((c : G))⁻¹ * v * ((c : G)) ∈ X := Work.ThreePoints.mem_conj_iff.mp hv
    rwa [← h2] at hvc
  -- ## Step 7: `u ∈ X = P ⊔ C_G(P)` and `u² = 1` force `u ∈ C_G(P)`
  have hnormC : ∀ x ∈ X, ∀ k ∈ C, x * k * x⁻¹ ∈ C := by
    intro x hx k hk
    rw [Subgroup.mem_centralizer_iff] at hk ⊢
    intro y hy
    have hxM : x ∈ M := hXM hx
    have hy' : x⁻¹ * y * x ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (M.inv_mem hxM) y).mp hy
    have h := hk (x⁻¹ * y * x) hy'
    have h2 := congrArg (fun t => x * t * x⁻¹) h
    have e1 : x * ((x⁻¹ * y * x) * k) * x⁻¹ = y * (x * k * x⁻¹) := by group
    have e2 : x * (k * (x⁻¹ * y * x)) * x⁻¹ = (x * k * x⁻¹) * y := by group
    rwa [e1, e2] at h2
  obtain ⟨p₀, hp₀P, c₀, hc₀C, hpc⟩ := exists_mul_mem_of_mem_sup hnormC huX
  have hcent : c₀ * p₀ = p₀ * c₀ := (Subgroup.mem_centralizer_iff.mp hc₀C p₀ hp₀P).symm
  have hp₀sq : p₀ * p₀ ∈ C := by
    have h2 : p₀ * c₀ * (p₀ * c₀) = 1 := by
      rw [hpc]; exact Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two hu2
    have h1 : p₀ * p₀ * (c₀ * c₀) = p₀ * c₀ * (p₀ * c₀) := by
      have e : p₀ * c₀ * (p₀ * c₀) = p₀ * (c₀ * p₀) * c₀ := by group
      rw [e, hcent]
      group
    have h1' : p₀ * p₀ * (c₀ * c₀) = 1 := by rw [h1]; exact h2
    have h5 : p₀ * p₀ = (c₀ * c₀)⁻¹ := eq_inv_of_mul_eq_one_left h1'
    rw [h5]
    exact C.inv_mem (C.mul_mem hc₀C hc₀C)
  have hp₀C : p₀ ∈ C := mem_centralizer_of_sq_mem_centralizer hPodd hp₀P hp₀sq
  have huC : u ∈ C := by
    rw [← hpc]
    exact C.mul_mem hp₀C hc₀C
  -- ## conclusion
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.mp huC) x hx).symm

end Work.ThreePoints.ThmC

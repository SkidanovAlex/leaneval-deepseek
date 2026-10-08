import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.T_sig_facts
import Submission.Work.ThmF.ChV3.Prove.P_on_L
import Submission.Work.ThmF.ChV3.Prove.A_LV_facts
import Submission.Work.ThmF.ChV3.Prove.cst_center_sylow
import Submission.Work.ThmF.ChV3.Prove.cst_isPGroup
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts
import Submission.Work.ThmF.ChV3.Prove.A_LV_aux
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.A_le_cst
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs
import Submission.Work.ThmF.Prove.centDLowerCentralizerS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.A_stronglyReal_normalizer` — Peterfalvi II Ch. V §3, step (16)

The strongly real elements of `A = Z₁ P Σ` all lie in `Z₁ = ⟨st⟩`, and `N_G(A) = C_G(st)⟨s⟩`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary helper lemmas -/

/-- Conjugation preserves strong reality. -/
lemma conj_StronglyReal {x u : G} (h : Work.ThmF.ChV3.StronglyReal x) :
    Work.ThmF.ChV3.StronglyReal (u * x * u⁻¹) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  refine ⟨u * a * u⁻¹, u * b * u⁻¹, ?_, ?_, ?_⟩
  · calc (u * a * u⁻¹) * (u * a * u⁻¹) = u * (a * a) * u⁻¹ := by group
      _ = 1 := by rw [ha]; group
  · calc (u * b * u⁻¹) * (u * b * u⁻¹) = u * (b * b) * u⁻¹ := by group
      _ = 1 := by rw [hb]; group
  · calc (u * a * u⁻¹) * (u * b * u⁻¹) = u * (a * b) * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hab]

/-- `S ≤ C(H)` and `S ≤ C(K)` imply `S ≤ C(H ⊔ K)`. -/
lemma le_centralizer_sup {H K S : Subgroup G}
    (hH : S ≤ Subgroup.centralizer (H : Set G))
    (hK : S ≤ Subgroup.centralizer (K : Set G)) :
    S ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hHs : H ≤ Subgroup.centralizer ({s} : Set G) := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hH hs) h hh)
  have hKs : K ≤ Subgroup.centralizer ({s} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hK hs) k hk)
  exact Subgroup.mem_centralizer_singleton_iff.mp (sup_le hHs hKs hy)

/-- A join of two commuting subgroups of exponent dividing `n` has exponent dividing `n`. -/
lemma pow_eq_one_of_mem_sup {H K : Subgroup G} {n : ℕ}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (hH : ∀ x ∈ H, x ^ n = 1) (hK : ∀ x ∈ K, x ^ n = 1) :
    ∀ x ∈ H ⊔ K, x ^ n = 1 := by
  have hKn : K ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk h hh
    have hkh : k * h * k⁻¹ = h := by rw [← hcomm h hh k hk]; group
    rw [hkh]
    exact hh
  have hcoe : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hKn
  intro x hx
  have hx' : x ∈ (H : Set G) * (K : Set G) := by rw [← hcoe]; exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨h, hh, k, hk, rfl⟩ := hx'
  rw [Commute.mul_pow ((commute_iff_eq h k).mpr (hcomm h hh k hk)) n, hH h hh, hK k hk, one_mul]

/-- Decompose an element of a join along a normal factor. -/
lemma exists_mul_of_mem_sup {H K : Subgroup G} (h : K ≤ Subgroup.normalizer (H : Set G))
    {x : G} (hx : x ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hcoe : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K h
  have hx' : x ∈ (H : Set G) * (K : Set G) := by rw [← hcoe]; exact hx
  rwa [Set.mem_mul] at hx'

/-- Conjugation of `z * v` by powers of `y`, when `y * v * y⁻¹ = c * v`, `c` commutes with
`y` and `v`, and `z` commutes with `y`. -/
lemma conj_pow_mul {y v c z : G} (hyc : c * y = y * c) (hcv : c * v = v * c)
    (hzy : z * y = y * z) (hyv : y * v * y⁻¹ = c * v) (k : ℕ) :
    y ^ k * (z * v) * (y ^ k)⁻¹ = (z * c ^ k) * v := by
  have hyz : y * z * y⁻¹ = z := by rw [← hzy]; group
  have hyc'' : y * c * y⁻¹ = c := by rw [← hyc]; group
  have hkey : ∀ k : ℕ, y * c ^ k * y⁻¹ = c ^ k := by
    intro k
    calc y * c ^ k * y⁻¹ = (MulAut.conj y) (c ^ k) := by simp [MulAut.conj_apply]
      _ = ((MulAut.conj y) c) ^ k := map_pow _ _ _
      _ = c ^ k := by rw [show (MulAut.conj y) c = c by rw [MulAut.conj_apply]; exact hyc'']
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : y ^ (k + 1) * (z * v) * (y ^ (k + 1))⁻¹ =
        y * (y ^ k * (z * v) * (y ^ k)⁻¹) * y⁻¹ := by
      rw [pow_succ']; group
    rw [hstep, ih]
    calc y * (z * c ^ k * v) * y⁻¹
        = (y * z * y⁻¹) * (y * c ^ k * y⁻¹) * (y * v * y⁻¹) := by group
      _ = z * c ^ k * (c * v) := by rw [hyz, hkey k, hyv]
      _ = z * c ^ (k + 1) * v := by rw [pow_succ']; group

/-- A subgroup all of whose elements commute with `s` is fixed by conjugation by `s`. -/
lemma map_conj_eq_of_mem_centralizer {s : G} {H : Subgroup G}
    (h : s ∈ Subgroup.centralizer (H : Set G)) :
    H.map (MulAut.conj s).toMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have hyc : y * s = s * y := Subgroup.mem_centralizer_iff.mp h y hy
    have h2 : (MulAut.conj s).toMonoidHom y = y := by
      have h1 : (MulAut.conj s).toMonoidHom y = s * y * s⁻¹ := by simp [MulAut.conj_apply]
      rw [h1, ← hyc]; group
    rwa [h2]
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨s⁻¹ * x * s, ?_, ?_⟩
    · have hx1 : x * s = s * x := Subgroup.mem_centralizer_iff.mp h x hx
      have h2 : s⁻¹ * x * s = x := by
        apply mul_left_cancel (a := s)
        rw [show s * (s⁻¹ * x * s) = x * s by group]
        exact hx1
      rw [h2]; exact hx
    · have h3 : (MulAut.conj s).toMonoidHom (s⁻¹ * x * s) = s * (s⁻¹ * x * s) * s⁻¹ := by
        simp [MulAut.conj_apply]
      rw [h3]; group

/-- `s * (s * a * s⁻¹) * s⁻¹ = a` for an involution `s`. -/
lemma conj_involution {s a : G} (hs : s * s = 1) : s * (s * a * s⁻¹) * s⁻¹ = a := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [hsinv]
  rw [show s * (s * a * s) * s = (s * s) * a * (s * s) by group, hs, one_mul, mul_one]

/-- In a cyclic group of order `3` generated by `x`, any two elements `z`, `c ≠ 1` satisfy
`z * c ^ k = 1` for some `k : ℕ`. -/
lemma exists_pow_mul_eq_one {x c z : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hc : c ∈ Subgroup.zpowers x) (hc1 : c ≠ 1) (hz : z ∈ Subgroup.zpowers x) :
    ∃ k : ℕ, z * c ^ k = 1 := by
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hcord : orderOf c = 3 := by
    have hdvd : orderOf c ∣ orderOf x := by
      have h1 : orderOf c ∣ Nat.card ↥(Subgroup.zpowers x) := Subgroup.orderOf_dvd_natCard _ hc
      rwa [Nat.card_zpowers] at h1
    rw [hxord] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hc3 : c ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hcord])
  have hceq : Subgroup.zpowers c = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hcord, hxord])
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hceq ▸ hz)
  have hc3z : c ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hc3
  have hjred : c ^ j = c ^ (j % 3) := zpow_eq_zpow_emod j hc3z
  have hjm3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by
    have h0 := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
    omega
  rcases hjm3 with h | h | h
  · have hz1 : z = 1 := by rw [← hj, hjred, h, zpow_zero]
    exact ⟨0, by rw [hz1, pow_zero, mul_one]⟩
  · have hz1 : z = c := by rw [← hj, hjred, h, zpow_one]
    exact ⟨2, by rw [hz1, (pow_succ' c 2).symm]; exact hc3⟩
  · have hz1 : z = c ^ 2 := by rw [← hj, hjred, h, zpow_ofNat]
    exact ⟨1, by rw [hz1, pow_one, (pow_succ c 2).symm]; exact hc3⟩

/-- `N_G(⟨s*t⟩) ≤ C_G(st) ⟨s⟩`, when `st` has order `3` and `s` (an involution) inverts it. -/
lemma NG_zpowers_le_Cst_sup {s t : G} (h3 : (s * t) ^ 3 = 1) (hne : s * t ≠ 1)
    (hinv : s * (s * t) * s⁻¹ = (s * t)⁻¹) :
    Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Z1 s t) ≤
      Work.ThmF.ChV3.Cst s t ⊔ Subgroup.zpowers s := by
  intro g hg
  have hdvd : orderOf (s * t) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
  have hord : orderOf (s * t) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hzZ : g * (s * t) * g⁻¹ ∈ Work.ThmF.ChV3.Z1 s t :=
    (Subgroup.mem_normalizer_iff.mp hg (s * t)).mp (Subgroup.mem_zpowers _)
  have hzord : orderOf (g * (s * t) * g⁻¹) = 3 := by
    have h1 : (MulAut.conj g).toMonoidHom (s * t) = g * (s * t) * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [← h1, orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (s * t), hord]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzZ
  have hx3 : (s * t) ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact h3
  have hjred : (s * t) ^ j = (s * t) ^ (j % 3) := zpow_eq_zpow_emod j hx3
  have hjm3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by
    have h0 := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
    omega
  rcases hjm3 with hk0 | hk1 | hk2
  · exfalso
    have heq : g * (s * t) * g⁻¹ = 1 := by rw [← hj, hjred, hk0, zpow_zero]
    rw [heq, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  · have hgx : g * (s * t) * g⁻¹ = s * t := by rw [← hj, hjred, hk1, zpow_one]
    have hcomm : g * (s * t) = (s * t) * g := by
      have := congrArg (fun w => w * g) hgx
      simpa [mul_assoc] using this
    exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  · have hx2inv : (s * t) ^ 2 = (s * t)⁻¹ := by
      have h : (s * t) ^ 2 * (s * t) = 1 := by rw [← pow_succ]; exact h3
      exact (inv_eq_of_mul_eq_one_left h).symm
    have hgx : g * (s * t) * g⁻¹ = (s * t)⁻¹ := by rw [← hj, hjred, hk2, zpow_ofNat, hx2inv]
    have hgsx : (g * s) * (s * t) * (g * s)⁻¹ = s * t := by
      calc (g * s) * (s * t) * (g * s)⁻¹ = g * (s * (s * t) * s⁻¹) * g⁻¹ := by group
        _ = g * (s * t)⁻¹ * g⁻¹ := by rw [hinv]
        _ = (g * (s * t) * g⁻¹)⁻¹ := by group
        _ = ((s * t)⁻¹)⁻¹ := by rw [hgx]
        _ = s * t := inv_inv _
    have hcomm : (g * s) * (s * t) = (s * t) * (g * s) := by
      have := congrArg (fun w => w * (g * s)) hgsx
      simpa [mul_assoc] using this
    have hgsC : g * s ∈ Work.ThmF.ChV3.Cst s t :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hg' : g = (g * s) * s⁻¹ := by group
    rw [hg']
    exact (Work.ThmF.ChV3.Cst s t ⊔ Subgroup.zpowers s).mul_mem
      (Subgroup.mem_sup_left hgsC)
      (Subgroup.mem_sup_right ((Subgroup.zpowers s).inv_mem (Subgroup.mem_zpowers s)))

/-! ## The main theorem -/

theorem A_stronglyReal_normalizer {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    (∀ g : G, ∀ a ∈ Work.ThmF.ChV3.Asub H P s t,
        Work.ThmF.ChV3.StronglyReal (g * a * g⁻¹) → a ∈ Work.ThmF.ChV3.Z1 s t) ∧
      Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Asub H P s t) =
        Work.ThmF.ChV3.Cst s t ⊔ Subgroup.zpowers s := by
  classical
  -- ## 0. Basic facts
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [c.s_inv, pow_two] at h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [c.split.invol, pow_two] at h
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hst3 : (s * t) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (s * t); rwa [d.f3] at h
  have hst_ne : s * t ≠ 1 := by
    intro h
    have h2 : orderOf (s * t) = 1 := by rw [h, orderOf_one]
    rw [d.f3] at h2
    exact absurd h2 (by norm_num)
  have hsst : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [hs_inv, mul_inv_rev, hs_inv, ht_inv]
    rw [show s * (s * t) * s = (s * s) * (t * s) by group, hs2, one_mul]
  have hZ1ord : orderOf (s * t) = 3 := by
    have hdvd : orderOf (s * t) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hst3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hst_ne
    · exact h
  have hZ1card : Nat.card ↥(Work.ThmF.ChV3.Z1 s t) = 3 := by
    rw [Work.ThmF.ChV3.Z1, Nat.card_zpowers, hZ1ord]
  have hVs : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  have hVt : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({t} : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp hx).2
  have hVleCst : Submission.Blueprint.centD H t ≤ Work.ThmF.ChV3.Cst s t :=
    (le_inf hVs hVt).trans (centralizer_mul_le_centralizer s t)
  -- ## 1. `A` is a join of three commuting subgroups of exponent `3`
  have hZ1P : Work.ThmF.ChV3.Z1 s t ≤ Subgroup.centralizer (P : Set G) := Z1_le_centralizer_P c
  have hZ1Sig : Work.ThmF.ChV3.Z1 s t ≤ Subgroup.centralizer (Work.ThmF.ChV3.Sig H t P : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr (fun σ hσ =>
      Subgroup.mem_centralizer_iff.mp (Z1_le_centralizer_W hC4 c hz) σ (Sig_le_W hσ))
  have hZ1PS : Work.ThmF.ChV3.Z1 s t ≤
      Subgroup.centralizer (((P ⊔ Work.ThmF.ChV3.Sig H t P : Subgroup G)) : Set G) :=
    le_centralizer_sup hZ1P hZ1Sig
  have hPScomm : ∀ x ∈ P, ∀ y ∈ Work.ThmF.ChV3.Sig H t P, x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp (Sig_le_centralizer_P hy) x hx
  have hPpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ 3 := by
      have h1 : orderOf x ∣ Nat.card ↥P := Subgroup.orderOf_dvd_natCard P hx
      rwa [d.p3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hSigpow : ∀ x ∈ Work.ThmF.ChV3.Sig H t P, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ 3 := by
      have h1 : orderOf x ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) :=
        Subgroup.orderOf_dvd_natCard _ hx
      rwa [d.sig3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hPSpow : ∀ x ∈ P ⊔ Work.ThmF.ChV3.Sig H t P, x ^ 3 = 1 :=
    pow_eq_one_of_mem_sup hPScomm hPpow hSigpow
  have hZ1pow : ∀ x ∈ Work.ThmF.ChV3.Z1 s t, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ 3 := by
      have h1 : orderOf x ∣ Nat.card ↥(Work.ThmF.ChV3.Z1 s t) :=
        Subgroup.orderOf_dvd_natCard _ hx
      rwa [hZ1card] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hZ1PScomm : ∀ z ∈ Work.ThmF.ChV3.Z1 s t,
      ∀ y ∈ P ⊔ Work.ThmF.ChV3.Sig H t P, z * y = y * z :=
    fun z hz y hy => (Subgroup.mem_centralizer_iff.mp (hZ1PS hz) y hy).symm
  have hA_pow3 : ∀ a ∈ Work.ThmF.ChV3.Asub H P s t, a ^ 3 = 1 := by
    intro a ha
    have hAeq : Work.ThmF.ChV3.Asub H P s t =
        Work.ThmF.ChV3.Z1 s t ⊔ (P ⊔ Work.ThmF.ChV3.Sig H t P) :=
      sup_assoc (Work.ThmF.ChV3.Z1 s t) P (Work.ThmF.ChV3.Sig H t P)
    rw [hAeq] at ha
    exact pow_eq_one_of_mem_sup hZ1PScomm hZ1pow hPSpow a ha
  -- ## 2. `s * t ∈ T`, `T` abelian
  have hS2 : ∀ g ∈ Work.ThmF.ChV3.CG P, g * s * g⁻¹ * s⁻¹ ∈ h15.R :=
    S2_commS_mem_R hFT hC4 c hpf (S1_centralizerP_eq hFT hC4 c h15 h7 hpf).2.1 h15.hRn
  have hTR : T ≤ h15.R := by rw [← h11.TPR]; exact le_sup_left
  have hPR : P ≤ h15.R := by rw [← h11.TPR]; exact le_sup_right
  obtain ⟨hTinv, hstT, hTexp, hTcard⟩ :=
    S3_T_facts hFT hC4 c hpf h15.m h15.hm h11 h7 h15.hcardR h15.hcq hS2
  have hZ1T : Work.ThmF.ChV3.Z1 s t ≤ T := Subgroup.zpowers_le.mpr hstT
  -- ## 3. Part (i): a conjugate of `a ∈ A − Z₁` lies in `(P Σ)^#`
  have hconj_to_PSig : ∀ a ∈ Work.ThmF.ChV3.Asub H P s t, a ∉ Work.ThmF.ChV3.Z1 s t →
      ∃ h : G, ∃ v ∈ P ⊔ Work.ThmF.ChV3.Sig H t P, v ≠ 1 ∧ h * a * h⁻¹ = v := by
    intro a ha hZ
    have hZ1norm : Work.ThmF.ChV3.Z1 s t ≤
        Subgroup.normalizer (((P ⊔ Work.ThmF.ChV3.Sig H t P : Subgroup G)) : Set G) :=
      hZ1PS.trans (Subgroup.centralizer_le_normalizer _)
    have ha' : a ∈ (P ⊔ Work.ThmF.ChV3.Sig H t P) ⊔ Work.ThmF.ChV3.Z1 s t := by
      have hAeq : Work.ThmF.ChV3.Asub H P s t =
          (P ⊔ Work.ThmF.ChV3.Sig H t P) ⊔ Work.ThmF.ChV3.Z1 s t := by
        rw [Work.ThmF.ChV3.Asub]; ac_rfl
      rwa [hAeq] at ha
    obtain ⟨v, hv, z, hz, hvz⟩ := exists_mul_of_mem_sup hZ1norm ha'
    have hzv : z * v = a := by
      rw [← hvz]
      exact (Subgroup.mem_centralizer_iff.mp (hZ1PS hz) v hv).symm
    have hv1 : v ≠ 1 := by
      intro h
      apply hZ
      rw [← hzv, h, mul_one]
      exact hz
    have hSigNorm : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (P : Set G) :=
      Sig_le_centralizer_P.trans (Subgroup.centralizer_le_normalizer (P : Set G))
    obtain ⟨p, hp, σ, hσ, hpσ⟩ := exists_mul_of_mem_sup hSigNorm hv
    by_cases hσ1 : σ = 1
    · -- ## 3a. `v = p ∈ P^#`: conjugate by an element of `L`
      have hvp : v = p := by rw [← hpσ, hσ1, mul_one]
      have hp1 : p ≠ 1 := fun h => hv1 (by rw [hvp, h])
      have hpord : orderOf p = 3 := by
        have hdvd : orderOf p ∣ 3 := by
          have h1 : orderOf p ∣ Nat.card ↥P := Subgroup.orderOf_dvd_natCard P hp
          rwa [d.p3] at h1
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hp1
        · exact h
      obtain ⟨hPL1, hPL2⟩ := P_on_L hFT hC4 c h15 h7 hpf h11 d
      obtain ⟨x₀, hx0P, y₀, hy0L, hx0y0⟩ := hPL1
      have hy0v : y₀ * p * y₀⁻¹ ≠ p := by
        intro hyp
        have hpp : Subgroup.zpowers p = P :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hp)
            (by rw [Nat.card_zpowers, hpord, d.p3])
        have hx0v : x₀ ∈ Subgroup.zpowers p := by rw [hpp]; exact hx0P
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx0v
        have hconj : y₀ * x₀ * y₀⁻¹ = x₀ := by
          rw [← hm]
          have h1 : y₀ * p ^ m * y₀⁻¹ = (MulAut.conj y₀) (p ^ m) := by
            simp [MulAut.conj_apply]
          rw [h1, map_zpow,
            show (MulAut.conj y₀) p = p by rw [MulAut.conj_apply, hyp]]
        have hcomm : x₀ * y₀ = y₀ * x₀ := by
          have h := congrArg (fun w => w * y₀) hconj
          simp only [mul_assoc, inv_mul_cancel, mul_one] at h
          exact h.symm
        exact hx0y0 hcomm
      have hccZ : y₀ * p * y₀⁻¹ * p⁻¹ ∈ Work.ThmF.ChV3.Z1 s t := hPL2 y₀ hy0L p hp
      have hcc1 : y₀ * p * y₀⁻¹ * p⁻¹ ≠ 1 := fun h => hy0v (mul_inv_eq_one.mp h)
      have hyv : y₀ * p * y₀⁻¹ = (y₀ * p * y₀⁻¹ * p⁻¹) * p := by group
      obtain ⟨k, hk⟩ := exists_pow_mul_eq_one hst3 hst_ne hccZ hcc1 hz
      have hyz : z * y₀ = y₀ * z :=
        (Subgroup.mem_centralizer_iff.mp
          (Z1_le_centralizer_Lsub hFT hC4 c h15 d hz) y₀ hy0L).symm
      have hcy : (y₀ * p * y₀⁻¹ * p⁻¹) * y₀ = y₀ * (y₀ * p * y₀⁻¹ * p⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp
          (Z1_le_centralizer_Lsub hFT hC4 c h15 d hccZ) y₀ hy0L).symm
      have hcv : (y₀ * p * y₀⁻¹ * p⁻¹) * p = p * (y₀ * p * y₀⁻¹ * p⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hZ1P hccZ) p hp).symm
      have hconj := conj_pow_mul hcy hcv hyz hyv k
      refine ⟨y₀ ^ k, v, hv, hv1, ?_⟩
      rw [← hzv, hvp, hconj, hk, one_mul]
    · -- ## 3b. `σ ≠ 1`: conjugate by an element of `T`
      obtain ⟨hT1, hT2, -⟩ := T_sig_facts hFT hC4 c h15 h7 hpf h11 d
      obtain ⟨x, hxT, hxσ⟩ := hT1 σ hσ hσ1
      have hccZ : x * σ * x⁻¹ * σ⁻¹ ∈ Work.ThmF.ChV3.Z1 s t := hT2 x hxT σ hσ
      have hcc1 : x * σ * x⁻¹ * σ⁻¹ ≠ 1 := by
        intro h
        apply hxσ
        have h2 : x * σ * x⁻¹ = σ := by
          have h' : (x * σ * x⁻¹ * σ⁻¹) * σ = 1 * σ := by rw [h, one_mul]
          rwa [show (x * σ * x⁻¹ * σ⁻¹) * σ = x * σ * x⁻¹ by group, one_mul] at h'
        have h3 : x * σ = σ * x := by
          have := congrArg (fun w => w * x) h2
          simpa [mul_assoc] using this
        rw [← h3]; group
      have hxp : x * p = p * x := mul_comm_of_mem h11.comm (hTR hxT) (hPR hp)
      have hcp : (x * σ * x⁻¹ * σ⁻¹) * p = p * (x * σ * x⁻¹ * σ⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hZ1P hccZ) p hp).symm
      have hcσ : σ * (x * σ * x⁻¹ * σ⁻¹) = (x * σ * x⁻¹ * σ⁻¹) * σ :=
        Subgroup.mem_centralizer_iff.mp (Z1_le_centralizer_W hC4 c hccZ) σ (Sig_le_W hσ)
      have hxv : x * v * x⁻¹ = (x * σ * x⁻¹ * σ⁻¹) * v := by
        have hstep : x * v * x⁻¹ = p * (x * σ * x⁻¹) := by
          rw [← hpσ]
          rw [show x * (p * σ) * x⁻¹ = (x * p * x⁻¹) * (x * σ * x⁻¹) by group]
          rw [show x * p * x⁻¹ = p by rw [hxp]; group]
        rw [hstep, show x * σ * x⁻¹ = (x * σ * x⁻¹ * σ⁻¹) * σ by group, ← hpσ]
        rw [show p * ((x * σ * x⁻¹ * σ⁻¹) * σ) = (p * (x * σ * x⁻¹ * σ⁻¹)) * σ by group,
            ← hcp]
        group
      obtain ⟨k, hk⟩ := exists_pow_mul_eq_one hst3 hst_ne hccZ hcc1 hz
      have hzx : z * x = x * z := mul_comm_of_mem h11.comm (hTR (hZ1T hz)) (hTR hxT)
      have hcx : (x * σ * x⁻¹ * σ⁻¹) * x = x * (x * σ * x⁻¹ * σ⁻¹) :=
        mul_comm_of_mem h11.comm (hTR (hZ1T hccZ)) (hTR hxT)
      have hcv : (x * σ * x⁻¹ * σ⁻¹) * v = v * (x * σ * x⁻¹ * σ⁻¹) := by
        rw [← hpσ]
        rw [show (x * σ * x⁻¹ * σ⁻¹) * (p * σ) = ((x * σ * x⁻¹ * σ⁻¹) * p) * σ by group,
            show (p * σ) * (x * σ * x⁻¹ * σ⁻¹) = p * (σ * (x * σ * x⁻¹ * σ⁻¹)) by group,
            hcp, hcσ]
        group
      have hconj := conj_pow_mul hcx hcv hzx hxv k
      refine ⟨x ^ k, v, hv, hv1, ?_⟩
      rw [← hzv]
      rw [hconj, hk, one_mul]
  -- ## 4. Part (1): strongly real elements of `A` lie in `Z₁`
  have hPart1 : ∀ g : G, ∀ a ∈ Work.ThmF.ChV3.Asub H P s t,
      Work.ThmF.ChV3.StronglyReal (g * a * g⁻¹) → a ∈ Work.ThmF.ChV3.Z1 s t := by
    intro g a ha hsr
    by_contra hZ
    obtain ⟨h, v, hv, hv1, hhav⟩ := hconj_to_PSig a ha hZ
    have hvV : v ∈ Submission.Blueprint.centD H t :=
      sup_le c.P_le (Sig_le_W.trans (W_le_centD H t)) hv
    have hsr' : Work.ThmF.ChV3.StronglyReal ((g * h⁻¹) * v * (g * h⁻¹)⁻¹) := by
      have heq : (g * h⁻¹) * v * (g * h⁻¹)⁻¹ = g * a * g⁻¹ := by rw [← hhav]; group
      rw [heq]
      exact hsr
    exact S4_centD_not_stronglyReal hC4 c v hvV hv1 (g * h⁻¹) hsr'
  -- ## 5. `C_G(st) ≤ N_G(A)` and `s ∈ N_G(A)`
  obtain ⟨hAcomm, hAcard, hZ1PSbot, hLVcard, hAleLV, hLVomega, hcent⟩ :=
    A_LV_facts hFT hC4 c h15 h7 hpf h11 d
  have hLVleCst : Lsub H s t ⊔ Submission.Blueprint.centD H t ≤ Work.ThmF.ChV3.Cst s t :=
    sup_le Lsub_le_Cst hVleCst
  have hCst_le_N : Work.ThmF.ChV3.Cst s t ≤
      Subgroup.normalizer (Work.ThmF.ChV3.Asub H P s t : Set G) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcst3 : IsPGroup 3 ↥(Work.ThmF.ChV3.Cst s t) := cst_isPGroup hFT hC4 c h15 d
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hcst3
    have hCstCard : Nat.card ↥(Work.ThmF.ChV3.Cst s t) = 3 ^ 4 * Nat.card ↥(W H t) := by
      rw [(cst_center_sylow hFT hC4 c h15 h7 hpf h11 d).2, d.G3]
    have hWpos : 0 < Nat.card ↥(W H t) := by rcases d.W39 with h | h <;> omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      rw [hCstCard] at hk
      omega
    have hKcard : Nat.card ↥((Lsub H s t ⊔ Submission.Blueprint.centD H t).subgroupOf
        (Work.ThmF.ChV3.Cst s t)) = Nat.card ↥(Lsub H s t ⊔ Submission.Blueprint.centD H t) := by
      have h1 := Subgroup.card_map_of_injective
        (K := (Lsub H s t ⊔ Submission.Blueprint.centD H t).subgroupOf (Work.ThmF.ChV3.Cst s t))
        (f := (Work.ThmF.ChV3.Cst s t).subtype) (fun a b hab => Subtype.ext hab)
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLVleCst] at h1
      exact h1.symm
    have hKidx : ((Lsub H s t ⊔ Submission.Blueprint.centD H t).subgroupOf
        (Work.ThmF.ChV3.Cst s t)).index = 3 := by
      have hmul := Subgroup.index_mul_card
        ((Lsub H s t ⊔ Submission.Blueprint.centD H t).subgroupOf (Work.ThmF.ChV3.Cst s t))
      rw [hKcard, hLVcard, hCstCard] at hmul
      have hcancel : ((Lsub H s t ⊔ Submission.Blueprint.centD H t).subgroupOf
          (Work.ThmF.ChV3.Cst s t)).index * (27 * Nat.card ↥(W H t)) =
          3 * (27 * Nat.card ↥(W H t)) := by
        rw [hmul]; ring
      exact Nat.mul_right_cancel (Nat.mul_pos (by norm_num) hWpos) hcancel
    have hKnormal : ((Lsub H s t ⊔ Submission.Blueprint.centD H t).subgroupOf
        (Work.ThmF.ChV3.Cst s t)).Normal := by
      refine Subgroup.normal_of_index_eq_minFac_card ?_
      rw [hKidx, hk, Nat.pow_minFac hk0]
      have hdvd : (3 : ℕ).minFac ∣ 3 := Nat.minFac_dvd 3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h (Nat.minFac_prime (show (3 : ℕ) ≠ 1 by norm_num)).ne_one
      · exact h.symm
    have hLVnormal : Work.ThmF.ChV3.Cst s t ≤
        Subgroup.normalizer ((Lsub H s t ⊔ Submission.Blueprint.centD H t : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLVleCst).mp hKnormal
    intro cc hcc
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro haA
      have haLV : a ∈ Lsub H s t ⊔ Submission.Blueprint.centD H t := hAleLV haA
      have h1 : cc * a * cc⁻¹ ∈ Lsub H s t ⊔ Submission.Blueprint.centD H t :=
        (Subgroup.mem_normalizer_iff.mp (hLVnormal hcc) a).mp haLV
      have hcubed : (cc * a * cc⁻¹) ^ 3 = cc * a ^ 3 * cc⁻¹ := by
        have h1 : cc * a * cc⁻¹ = (MulAut.conj cc) a := by rw [MulAut.conj_apply]
        rw [h1, ← map_pow (MulAut.conj cc) a 3, MulAut.conj_apply]
      exact hLVomega (cc * a * cc⁻¹) h1 (by
        rw [hcubed, hA_pow3 a haA]; group)
    · intro hca
      have haLV : cc⁻¹ * (cc * a * cc⁻¹) * cc ∈
          Lsub H s t ⊔ Submission.Blueprint.centD H t := by
        have hmem := (Subgroup.mem_normalizer_iff.mp
          (hLVnormal ((Work.ThmF.ChV3.Cst s t).inv_mem hcc))
          (cc * a * cc⁻¹)).mp (hAleLV hca)
        rwa [inv_inv] at hmem
      have heq : cc⁻¹ * (cc * a * cc⁻¹) * cc = a := by group
      rw [← heq]
      have hcubed : (cc⁻¹ * (cc * a * cc⁻¹) * cc) ^ 3 =
          cc⁻¹ * (cc * a * cc⁻¹) ^ 3 * cc := by
        have h1 : cc⁻¹ * (cc * a * cc⁻¹) * cc = (MulAut.conj cc⁻¹).toMonoidHom (cc * a * cc⁻¹) := by
          simp [MulAut.conj_apply]
        rw [h1, ← map_pow (MulAut.conj cc⁻¹).toMonoidHom (cc * a * cc⁻¹) 3]
        have h2 : (MulAut.conj cc⁻¹).toMonoidHom ((cc * a * cc⁻¹) ^ 3) =
            cc⁻¹ * (cc * a * cc⁻¹) ^ 3 * cc := by simp [MulAut.conj_apply]
        rw [h2]
      exact hLVomega _ haLV (by rw [hcubed, hA_pow3 (cc * a * cc⁻¹) hca]; group)
  have hPs : s ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.mp (hVs (c.P_le hp)))
  have hSigs : s ∈ Subgroup.centralizer (Work.ThmF.ChV3.Sig H t P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hVs (W_le_centD H t (Sig_le_W hx))))
  have hsA : ∀ x ∈ Work.ThmF.ChV3.Asub H P s t, s * x * s⁻¹ ∈ Work.ThmF.ChV3.Asub H P s t := by
    have hZ1map : (Work.ThmF.ChV3.Z1 s t).map (MulAut.conj s).toMonoidHom = Work.ThmF.ChV3.Z1 s t := by
      rw [Work.ThmF.ChV3.Z1, MonoidHom.map_zpowers]
      have hc : (MulAut.conj s).toMonoidHom (s * t) = (s * t)⁻¹ := by
        have h1 : (MulAut.conj s).toMonoidHom (s * t) = s * (s * t) * s⁻¹ := by simp [MulAut.conj_apply]
        rw [h1]; exact hsst
      rw [hc, Subgroup.zpowers_inv]
    have hPmap : (P).map (MulAut.conj s).toMonoidHom = P :=
      map_conj_eq_of_mem_centralizer (H := P) hPs
    have hSigmap : (Work.ThmF.ChV3.Sig H t P).map (MulAut.conj s).toMonoidHom =
        Work.ThmF.ChV3.Sig H t P :=
      map_conj_eq_of_mem_centralizer (H := Work.ThmF.ChV3.Sig H t P) hSigs
    have hmap : (Work.ThmF.ChV3.Asub H P s t).map (MulAut.conj s).toMonoidHom ≤
        Work.ThmF.ChV3.Asub H P s t := by
      rw [Work.ThmF.ChV3.Asub, Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [hZ1map]
        exact (le_sup_left : Work.ThmF.ChV3.Z1 s t ≤ Work.ThmF.ChV3.Z1 s t ⊔ P).trans
          (le_sup_left : Work.ThmF.ChV3.Z1 s t ⊔ P ≤
            (Work.ThmF.ChV3.Z1 s t ⊔ P) ⊔ Work.ThmF.ChV3.Sig H t P)
      · rw [hPmap]
        exact (le_sup_right : P ≤ Work.ThmF.ChV3.Z1 s t ⊔ P).trans
          (le_sup_left : Work.ThmF.ChV3.Z1 s t ⊔ P ≤
            (Work.ThmF.ChV3.Z1 s t ⊔ P) ⊔ Work.ThmF.ChV3.Sig H t P)
      · rw [hSigmap]
        exact le_sup_right
    intro x hx
    have := hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have h2 : (MulAut.conj s).toMonoidHom x = s * x * s⁻¹ := by simp [MulAut.conj_apply]
    rwa [h2] at this
  have hs_N : s ∈ Subgroup.normalizer (Work.ThmF.ChV3.Asub H P s t : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hsA a ha, fun ha => by
      have := hsA (s * a * s⁻¹) ha
      rwa [conj_involution (s := s) (a := a) hs2] at this⟩
  -- ## 6. `N_G(A) ≤ C_G(st) ⟨s⟩`
  have hPart2sub : Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Asub H P s t) ≤
      Work.ThmF.ChV3.Cst s t ⊔ Subgroup.zpowers s := by
    intro g hg
    have hstA : s * t ∈ Work.ThmF.ChV3.Asub H P s t :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hgst : g * (s * t) * g⁻¹ ∈ Work.ThmF.ChV3.Asub H P s t :=
      (Subgroup.mem_normalizer_iff.mp hg (s * t)).mp hstA
    have hst_sr : Work.ThmF.ChV3.StronglyReal (s * t) := ⟨s, t, hs2, ht2, rfl⟩
    have hsr : Work.ThmF.ChV3.StronglyReal (g * (s * t) * g⁻¹) := conj_StronglyReal (u := g) hst_sr
    have hsr' : Work.ThmF.ChV3.StronglyReal
        (g⁻¹ * (g * (s * t) * g⁻¹) * (g⁻¹)⁻¹) := by
      have heq : g⁻¹ * (g * (s * t) * g⁻¹) * (g⁻¹)⁻¹ = s * t := by group
      rw [heq]; exact hst_sr
    have h1 : g * (s * t) * g⁻¹ ∈ Work.ThmF.ChV3.Z1 s t := hPart1 g⁻¹ _ hgst hsr'
    have hgN : g ∈ Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Z1 s t) := by
      rw [← cj_eq_self_iff]
      have hzord : orderOf (g * (s * t) * g⁻¹) = 3 := by
        have h2 : (MulAut.conj g).toMonoidHom (s * t) = g * (s * t) * g⁻¹ := by
          simp [MulAut.conj_apply]
        rw [← h2, orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (s * t),
          hZ1ord]
      have hzpeq : Subgroup.zpowers (g * (s * t) * g⁻¹) = Work.ThmF.ChV3.Z1 s t := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h1) ?_
        have hcard1 : Nat.card ↥(Subgroup.zpowers (g * (s * t) * g⁻¹)) = 3 := by
          rw [Nat.card_zpowers, hzord]
        rw [hcard1, Work.ThmF.ChV3.Z1, Nat.card_zpowers, hZ1ord]
      show (Work.ThmF.ChV3.Z1 s t).map (MulAut.conj g).toMonoidHom = Work.ThmF.ChV3.Z1 s t
      rw [Work.ThmF.ChV3.Z1, MonoidHom.map_zpowers]
      have h3 : (MulAut.conj g).toMonoidHom (s * t) = g * (s * t) * g⁻¹ := by
        simp [MulAut.conj_apply]
      rw [h3]
      exact hzpeq
    exact NG_zpowers_le_Cst_sup hst3 hst_ne hsst hgN
  have hPart2sup : Work.ThmF.ChV3.Cst s t ⊔ Subgroup.zpowers s ≤
      Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Asub H P s t) :=
    sup_le hCst_le_N (Subgroup.zpowers_le.mpr hs_N)
  exact ⟨hPart1, le_antisymm hPart2sub hPart2sup⟩

end Work.ThmF.ChV3.Prove

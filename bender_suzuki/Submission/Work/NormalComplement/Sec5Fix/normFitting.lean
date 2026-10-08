import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.Coprime.All
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.NormalComplement.Sec5Fix.NF.three_le_fixedPts_centH
import Submission.Work.NormalComplement.Sec5Fix.NF.centH_conj_into_centD
import Submission.Work.NormalComplement.Sec5Fix.NF.fitting_le_centralizer
import Submission.Work.NormalComplement.Sec5Fix.NF.normalizer_fitSub_of_conj_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.NormalComplement.Sec5Fix

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- `F(V) = fitSub V` is normal in `V` (the Fitting subgroup of `↥V` is normal there). -/
theorem le_normalizer_fitSub {G : Type} [Group G] (V : Subgroup G) :
    V ≤ Subgroup.normalizer ((Work.NormalComplement.Design.fitSub V : Subgroup G) : Set G) := by
  have hN : (Work.Fitting.fitting ↥V).Normal :=
    Work.Fitting.normal_sSup (fun N hN => (Work.Fitting.mem_fittingSet.mp hN).1)
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(⟨v,hv⟩ : ↥V) * w * (⟨v,hv⟩ : ↥V)⁻¹,
      Subgroup.Normal.conj_mem hN w hw ⟨v,hv⟩, ?_⟩
    simp
  · rintro ⟨w, hw, hwv⟩
    have hmem : (⟨v,hv⟩:↥V)⁻¹ * w * (⟨v,hv⟩:↥V) ∈ Work.Fitting.fitting ↥V := by
      simpa [inv_inv] using Subgroup.Normal.conj_mem hN w hw (⟨v,hv⟩:↥V)⁻¹
    refine Subgroup.mem_map.mpr ⟨⟨v,hv⟩⁻¹ * w * ⟨v,hv⟩, hmem, ?_⟩
    have hwv' : (w : G) = v * h * v⁻¹ := hwv
    show v⁻¹ * ↑w * v = h
    rw [hwv']; group

/-- The normaliser of `M` normalises `O_{p'}(M)` for a prime `p` (characteristic subgroup). -/
theorem normalizer_le_normalizer_pPrimeCoreSub' {G : Type} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (M : Subgroup G) :
    Subgroup.normalizer (M : Set G) ≤
      Subgroup.normalizer ((Work.NormalComplement.pPrimeCoreSub p M : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have h := Work.ThreePoints.ThmC.pPrimeCoreSub_conj p hp M x
  simp only [Submission.Blueprint.conj] at h
  have hx' : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) M = M := hx
  rw [hx'] at h
  exact h.symm

/-- If `x` normalises `H` and `N`, then `x` normalises `C_G(N) ⊓ H`. -/
theorem normalizer_inf_centralizer {G : Type} [Group G] {H N : Subgroup G} {x : G}
    (hxH : x ∈ Subgroup.normalizer (H : Set G)) (hxN : x ∈ Subgroup.normalizer (N : Set G)) :
    x ∈ Subgroup.normalizer ((Subgroup.centralizer (N : Set G) ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxyH : y ∈ H ↔ x * y * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hxH) y
  have hxyN : ∀ n : G, n ∈ N ↔ x * n * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hxN)
  constructor
  · intro hy
    obtain ⟨hyC, hyH⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, (hxyH.mp hyH)⟩
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro n hn
    have hn' : x⁻¹ * n * x ∈ N := by
      refine (hxyN (x⁻¹ * n * x)).mpr ?_
      rwa [show x * (x⁻¹ * n * x) * x⁻¹ = n from by group]
    have hcomm := hyC (x⁻¹ * n * x) hn'
    calc n * (x * y * x⁻¹) = x * ((x⁻¹ * n * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * n * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * y * x⁻¹) * n := by group
  · intro hy
    obtain ⟨hyC, hyH⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, (hxyH.mpr hyH)⟩
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro n hn
    have hn' : x * n * x⁻¹ ∈ N := (hxyN n).mp hn
    have hcomm := hyC (x * n * x⁻¹) hn'
    calc n * y = x⁻¹ * ((x * n * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * n * x⁻¹)) * x := by rw [hcomm]
      _ = y * n := by group

/-- **Peterfalvi I Ch. III §5 Proposition 3** (p. 186): `N_H(P) ≤ N_H(F(V))`, in the form
consumed by the final contradiction (`sec5_final_aux`).

Assembly of the three pieces of §5 Prop. 3:
* `NF.centH_conj_into_centD`: `C_H(N)` is conjugate into `V` (Peterfalvi's "`C_H(N) ⊆ V^g`",
  obtained from Ch. II §4 Prop. 2(b) and the 2-transitivity `ThmAProp` on `G ⧸ H`);
* `NF.fitting_le_centralizer`: `F(V) ≤ C_H(N)` (App. VII);
* `NF.normalizer_fitSub_of_conj_le`: hence `F(V)` is the unique Sylow `r`-subgroup of `C_H(N)`,
  so it is characteristic there, and every `x ∈ N_H(P)` (which normalises `N = O_{f'}(M)` and
  hence `C_H(N)`) normalises `F(V)`. -/
theorem normFitting (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (hB : (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))))
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t)
    (hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hMc : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hMd : Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
      Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G)) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t) : Subgroup G) : Set G) := by
  classical
  letI : Fact r.Prime := ⟨h.r_prime⟩
  intro x hx
  obtain ⟨hxH, hxP⟩ := Subgroup.mem_inf.mp hx
  have hfprime : (orderOf (u * t)).Prime := by
    rcases hf with h3 | h5
    · rw [h3]; norm_num
    · rw [h5]; norm_num
  -- `x` normalises `N = O_{f'}(M)`
  have hxN : x ∈ Subgroup.normalizer
      ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G) :=
    normalizer_le_normalizer_pPrimeCoreSub' (orderOf (u * t)) hfprime M (hMc hx)
  -- `x` normalises `C = C_G(N) ⊓ H`
  have hxC : x ∈ Subgroup.normalizer
      (((Subgroup.centralizer
          ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G)) ⊓ H
        : Subgroup G) : Set G) :=
    normalizer_inf_centralizer (Subgroup.le_normalizer hxH) hxN
  -- `F(V) ≤ C_G(N)` (App. VII), hence `F(V) ≤ C`
  have hFCG : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      Subgroup.centralizer
        ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G) :=
    Work.NormalComplement.Sec5Fix.NF.fitting_le_centralizer
      hFT hVII h u hu hf hB M hM hMc hMd
  have hFC : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      (((Subgroup.centralizer
          ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G)) ⊓ H
        : Subgroup G)) :=
    le_inf hFCG (le_trans (Subgroup.map_subtype_le _) (le_trans inf_le_left inf_le_left))
  -- `C` is conjugate into `V` (Ch. II §4 Prop. 2(b) + 2-transitivity)
  obtain ⟨g, hg⟩ := Work.NormalComplement.Sec5Fix.NF.centH_conj_into_centD
    hFT hA hC4 hBP h u hu hf hB M hM hMab hMc hMd
  exact Work.NormalComplement.Sec5Fix.NF.normalizer_fitSub_of_conj_le hFC ⟨g, hg⟩ h.fitV_syl hxC

end Work.NormalComplement.Sec5Fix

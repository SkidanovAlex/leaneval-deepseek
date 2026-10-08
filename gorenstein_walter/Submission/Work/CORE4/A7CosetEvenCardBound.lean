import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.A7Fusion
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7M_eq
import Submission.Work.CORE4.A7K
import Submission.Work.CORE4.A7IndexH
import Submission.Work.CORE4.A7UMCard
import Submission.Work.CORE4.A7Normalize
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.AUTA7.A7.CentralizerOrderThree
import Submission.Work.CORE4E.A7CMACardBound

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-- **`A := C.D.F ⊔ C.D.K = B.U ⊓ C.D.M` is normalised by `H = B.U ⊔ B.S`.**

For `h ∈ H = U ⊔ S` we write `h = u * s` with `u ∈ U`, `s ∈ S`; then `A^u = A` because `A ⊴ U`
(`A7Facts5`), while `A = U ⊓ M` and `s ∈ S ≤ M`, `U^s = U` (as `U ⊴ H`) give `A^s = A`. -/
theorem A7_FK_normal_H (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (C : Work.GW2.Case2Ctx6 B)
    (hHyp : Work.GW2.Hyp9 G B C) (hA7 : Work.GW2.IsA7Case C.D)
    (h1 : Work.GW2.A7Facts1 C.D) (h2 : Work.GW2.A7Facts2 B C.D)
    (h3 : Work.GW2.A7Facts3 B C.D) (h5 : Work.GW2.A7Facts5 B C.D) :
    B.H ≤ Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  obtain ⟨_hM, hUM, _hU3card⟩ := A7M_eq I G B C ⟨hbc, hcase2, hplus, hseven, height⟩ hA7 h1 h2 h3 h5
  have hHsplit : B.H = B.U ⊔ (B.S : Subgroup G) := A7Split I hbc h2
  have hSleM : (B.S : Subgroup G) ≤ C.D.M := le_trans h2.2.2.1 (layerIn_le C.D.M)
  have hAnormU : ((C.D.F ⊔ C.D.K).subgroupOf B.U).Normal := h5.2.2
  have hAleU : (C.D.F ⊔ C.D.K) ≤ B.U := hUM ▸ inf_le_left
  have hUleN : B.U ≤ Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAleU).mp hAnormU
  have hSleN : (B.S : Subgroup G) ≤
      Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs a ha
    have hsH : s ∈ B.H := B.S_le_H hs
    have haUM : a ∈ B.U ⊓ C.D.M := by rw [hUM]; exact ha
    obtain ⟨haU, haM⟩ := Subgroup.mem_inf.mp haUM
    have hsU : s * a * s⁻¹ ∈ B.U :=
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a s haU hsH
    have hsM : s * a * s⁻¹ ∈ C.D.M :=
      C.D.M.mul_mem (C.D.M.mul_mem (hSleM hs) haM) (C.D.M.inv_mem (hSleM hs))
    rw [← hUM]
    exact Subgroup.mem_inf.mpr ⟨hsU, hsM⟩
  rw [hHsplit]
  exact sup_le hUleN hSleN

/-- `C.D.F` is commutative (it has order `3`). -/
theorem A7_F_isMulCommutative (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (C : Work.GW2.Case2Ctx6 B) (h1 : Work.GW2.A7Facts1 C.D) :
    IsMulCommutative ↥C.D.F := by
  have hFcard : Nat.card ↥C.D.F = 3 := h1.2.1
  obtain ⟨f, hfF, hf1⟩ := Case2Data.exists_ne_one_of_F B C.D (Case2Pre.F_ne B C.D C.pre)
  have hdvd : orderOf f ∣ Nat.card ↥C.D.F := Subgroup.orderOf_dvd_natCard C.D.F hfF
  rw [hFcard] at hdvd
  have hf3 : orderOf f = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hf1
    · exact h
  have hDFeq : C.D.F = Subgroup.zpowers f := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfF) ?_).symm
    rw [Nat.card_zpowers, hf3, hFcard]
  rw [hDFeq]
  infer_instance

/-- `C.D.F` is central in `C.D.M`: it centralises `E(M)` (`Case2Pre`) and is abelian, while
`M = E(M) ⊔ (F ⊔ K)`. -/
theorem A7_F_le_centralizer_M (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (C : Work.GW2.Case2Ctx6 B)
    (hHyp : Work.GW2.Hyp9 G B C) (hA7 : Work.GW2.IsA7Case C.D)
    (h1 : Work.GW2.A7Facts1 C.D) (h2 : Work.GW2.A7Facts2 B C.D)
    (h3 : Work.GW2.A7Facts3 B C.D) (h5 : Work.GW2.A7Facts5 B C.D) :
    C.D.F ≤ Subgroup.centralizer ((C.D.M : Subgroup G) : Set G) := by
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  have hM_eq : C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.F ⊔ C.D.K) :=
    (A7M_eq I G B C ⟨hbc, hcase2, hplus, hseven, height⟩ hA7 h1 h2 h3 h5).1
  have hFcentE : C.D.F ≤ Subgroup.centralizer ((Work.GW2.layerIn C.D.M : Subgroup G) : Set G) :=
    Case2Pre.F_cent B C.D C.pre
  have hFcommF : C.D.F ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (A7_F_isMulCommutative I B C h1)
  have hEleCF : Work.GW2.layerIn C.D.M ≤
      Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr hFcentE
  have hKleCF : C.D.K ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) :=
    le_trans (K_le_layerIn_of_prePlus hplus) hEleCF
  have hMleCF : C.D.M ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) := by
    rw [hM_eq]
    exact sup_le hEleCF (sup_le hFcommF hKleCF)
  exact Subgroup.le_centralizer_iff.mp hMleCF

/-- The image of the centre of a `y`-invariant subgroup `N` is `y`-invariant. -/
theorem conjSub_center_image_subset {N : Subgroup G} {y : G} (hyy : y * y = 1)
    (hNinv : ∀ n : G, n ∈ N → y * n * y⁻¹ ∈ N) :
    ∀ z : G, z ∈ (Subgroup.center ↥N).map N.subtype →
      y * z * y⁻¹ ∈ (Subgroup.center ↥N).map N.subtype := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  intro z hz
  rw [Subgroup.mem_map] at hz ⊢
  obtain ⟨a, ha, haz⟩ := hz
  have hzN : z ∈ N := by rw [← haz]; exact a.2
  refine ⟨⟨y * z * y⁻¹, hNinv z hzN⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  show (m : G) * (y * z * y⁻¹) = (y * z * y⁻¹) * (m : G)
  have hmN : y⁻¹ * (m : G) * y ∈ N := by
    have h := hNinv (m : G) m.2
    simpa [hyinv] using h
  have hcomm := Subgroup.mem_center_iff.mp ha ⟨y⁻¹ * (m : G) * y, hmN⟩
  have hcomm' : (y⁻¹ * (m : G) * y) * z = z * (y⁻¹ * (m : G) * y) := by
    rw [← haz]
    exact congrArg (fun w : ↥N => (w : G)) hcomm
  calc (m : G) * (y * z * y⁻¹) = y * ((y⁻¹ * (m : G) * y) * z) * y⁻¹ := by group
    _ = y * (z * (y⁻¹ * (m : G) * y)) * y⁻¹ := by rw [hcomm']
    _ = (y * z * y⁻¹) * (m : G) := by group

/-- **The main step**: for an involution `y ∈ H ∖ M`, `N := M ⊓ M^y` lies in the centraliser of
`A = F ⊔ K` in `M`.

`F ≤ Z(M)` (`A7_F_le_centralizer_M`) and `F ≤ A ≤ N`, so `F ≤ A ⊓ Z(N)`, and `A ⊓ Z(N)` is
`y`-invariant.  If `A ⊓ Z(N) = F` then `y` preserves `F`, i.e. `y ∈ N_G(F) = M`, contradiction;
as `3 ≤ |A ⊓ Z(N)|` and `|A ⊓ Z(N)| ∣ 9`, this forces `A ≤ Z(N)`, so every element of `N`
commutes with `A`. -/
theorem A7_coset_le_centralizer (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (C : Work.GW2.Case2Ctx6 B)
    (hHyp : Work.GW2.Hyp9 G B C) (hA7 : Work.GW2.IsA7Case C.D)
    (h1 : Work.GW2.A7Facts1 C.D) (h2 : Work.GW2.A7Facts2 B C.D)
    (h3 : Work.GW2.A7Facts3 B C.D) (h5 : Work.GW2.A7Facts5 B C.D)
    (y : G) (hy2 : orderOf y = 2) (hy_notM : y ∉ C.D.M) (hyH : y ∈ B.H) :
    C.D.M ⊓ Work.GW2.conjSub y C.D.M ≤
      Subgroup.centralizer ((C.D.F ⊔ C.D.K : Subgroup G) : Set G) := by
  classical
  have hFcard : Nat.card ↥C.D.F = 3 := h1.2.1
  have hKcard : Nat.card ↥C.D.K = 3 := h1.1
  have hB0F : C.D.B0 = C.D.F := h3.2.1
  have hAcard : Nat.card ↥(C.D.F ⊔ C.D.K : Subgroup G) = 9 := A7UMCard hB0F hKcard hFcard
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hAnormH := A7_FK_normal_H I B C hHyp hA7 h1 h2 h3 h5
  have hAy_sub : ∀ a ∈ (C.D.F ⊔ C.D.K : Subgroup G),
      y * a * y⁻¹ ∈ (C.D.F ⊔ C.D.K : Subgroup G) :=
    fun a ha => Subgroup.le_normalizer_iff.mp hAnormH y hyH a ha
  have hNinv : ∀ n : G, n ∈ C.D.M ⊓ Work.GW2.conjSub y C.D.M →
      y * n * y⁻¹ ∈ C.D.M ⊓ Work.GW2.conjSub y C.D.M := by
    intro n hn
    obtain ⟨hnM, hnC⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨a, haM, ha⟩ := (Work.CORE4.mem_conjSub_iff' C.D.M y n).mp hnC
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : y * n * y⁻¹ = a := by
        rw [← ha, hyinv]
        calc y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = a := by rw [hyy]; simp
      rw [heq]; exact haM
    · exact (Work.CORE4.mem_conjSub_iff' C.D.M y (y * n * y⁻¹)).mpr ⟨n, hnM, rfl⟩
  have hAleM : (C.D.F ⊔ C.D.K : Subgroup G) ≤ C.D.M := by
    rw [← (A7M_eq I G B C hHyp hA7 h1 h2 h3 h5).2.1]
    exact inf_le_right
  have hAle_conjM : (C.D.F ⊔ C.D.K : Subgroup G) ≤ Work.GW2.conjSub y C.D.M := by
    intro a ha
    refine (Work.CORE4.mem_conjSub_iff' C.D.M y a).mpr ⟨y⁻¹ * a * y, ?_, ?_⟩
    · have h := Subgroup.le_normalizer_iff.mp hAnormH y⁻¹ (B.H.inv_mem hyH) a ha
      rw [inv_inv] at h
      exact hAleM h
    · have heq : y * (y⁻¹ * a * y) * y⁻¹ = a := by group
      exact heq
  have hAleN : (C.D.F ⊔ C.D.K : Subgroup G) ≤ C.D.M ⊓ Work.GW2.conjSub y C.D.M :=
    le_inf hAleM hAle_conjM
  have hFZ : C.D.F ≤ Subgroup.centralizer ((C.D.M : Subgroup G) : Set G) :=
    A7_F_le_centralizer_M I B C hHyp hA7 h1 h2 h3 h5
  have hFZc : C.D.F ≤ (Subgroup.center ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M)).map
      (C.D.M ⊓ Work.GW2.conjSub y C.D.M).subtype := by
    intro f hf
    rw [Subgroup.mem_map]
    refine ⟨⟨f, ?_⟩, ?_, rfl⟩
    · exact hAleN (Subgroup.mem_sup_left hf)
    · rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hFZ hf)) (m : G) (Subgroup.mem_inf.mp m.2).1
  set Zc : Subgroup G :=
    (Subgroup.center ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M)).map
      (C.D.M ⊓ Work.GW2.conjSub y C.D.M).subtype with hZc
  have hFZc' : C.D.F ≤ Zc := by rw [hZc]; exact hFZc
  have hyZc : ∀ z : G, z ∈ Zc → y * z * y⁻¹ ∈ Zc := by
    intro z hz
    rw [hZc] at hz ⊢
    exact conjSub_center_image_subset hyy hNinv z hz
  set W : Subgroup G := (C.D.F ⊔ C.D.K : Subgroup G) ⊓ Zc with hW
  have hFW : C.D.F ≤ W := le_inf le_sup_left hFZc'
  have hWA : W ≤ (C.D.F ⊔ C.D.K : Subgroup G) := inf_le_left
  have hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro w hw
    obtain ⟨hwA, hwZ⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨hAy_sub w hwA, hyZc w hwZ⟩
  have hWcard_dvd : Nat.card ↥W ∣ 9 := by
    have h := Subgroup.card_dvd_of_le hWA
    rwa [hAcard] at h
  have hWcard : Nat.card ↥W = 3 ∨ Nat.card ↥W = 9 := by
    have hge : 3 ≤ Nat.card ↥W := by
      have h := Subgroup.card_dvd_of_le hFW
      rw [hFcard] at h
      exact Nat.le_of_dvd Nat.card_pos h
    have hp3 : Nat.Prime 3 := by norm_num
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (p := 3) hp3 (m := 2) (i := Nat.card ↥W)).mp
      (by simpa using hWcard_dvd)
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
    · rw [h, pow_zero] at hk; omega
    · left; rw [hk, h]; norm_num
    · right; rw [hk, h]; norm_num
  have hA_le_Z : (C.D.F ⊔ C.D.K : Subgroup G) ≤ Zc := by
    rcases hWcard with hc3 | hc9
    · exfalso
      have hWF : W = C.D.F := (Subgroup.eq_of_le_of_card_ge hFW (by rw [hFcard, hc3])).symm
      have hyF : ∀ x ∈ (C.D.F : Subgroup G), y * x * y⁻¹ ∈ C.D.F := by
        intro x hx
        have hxW : x ∈ W := hFW hx
        have hres := hyW x hxW
        rwa [hWF] at hres
      have hyNorm : y ∈ Subgroup.normalizer ((C.D.F : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hyF x
        · intro hx
          have h2 := hyF (y * x * y⁻¹) hx
          have heq : y * (y * x * y⁻¹) * y⁻¹ = x := by
            rw [hyinv]
            calc y * (y * x * y) * y = (y * y) * x * (y * y) := by group
              _ = x := by rw [hyy]; simp
          rwa [heq] at h2
      rw [Case2Pre.N_F B C.D C.pre] at hyNorm
      exact hy_notM hyNorm
    · have hWeq : W = (C.D.F ⊔ C.D.K : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hWA (by rw [hAcard, hc9])
      intro a ha
      have haW : a ∈ W := hWeq ▸ ha
      exact (Subgroup.mem_inf.mp haW).2
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haZ : a ∈ Zc := hA_le_Z ha
  rw [hZc, Subgroup.mem_map] at haZ
  obtain ⟨b, hb, hba⟩ := haZ
  have hcomm : (⟨n, hn⟩ : ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M)) * b = b * ⟨n, hn⟩ :=
    Subgroup.mem_center_iff.mp hb ⟨n, hn⟩
  have h2 : (n : G) * a = a * n := by
    have h4 : (C.D.M ⊓ Work.GW2.conjSub y C.D.M).subtype (⟨n, hn⟩ * b) =
        (C.D.M ⊓ Work.GW2.conjSub y C.D.M).subtype (b * ⟨n, hn⟩) := by rw [hcomm]
    rw [map_mul, map_mul, hba] at h4
    simpa using h4
  exact h2.symm

theorem A7CosetEvenCardBound (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.GW2.A7Facts3 B C.D → Work.GW2.A7Facts4 B C.D →
          Work.GW2.A7Facts5 B C.D →
            ∀ y : G, orderOf y = 2 → y ∉ C.D.M → y ∈ B.H →
              Nat.card ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M) ≤ 108 := by
  intro G _inst _fin B C hHyp hA7 h1 h2 h3 _h4 h5 y hy2 hy_notM hyH
  have hNsub : (C.D.M ⊓ Work.GW2.conjSub y C.D.M) ≤
      C.D.M ⊓ Subgroup.centralizer ((C.D.F ⊔ C.D.K : Subgroup G) : Set G) :=
    le_inf inf_le_left (A7_coset_le_centralizer I B C hHyp hA7 h1 h2 h3 h5 y hy2 hy_notM hyH)
  have hdvd := Subgroup.card_dvd_of_le hNsub
  refine le_trans (Nat.le_of_dvd Nat.card_pos hdvd) ?_
  exact Work.CORE4E.A7CMACardBound I G B C hHyp hA7 h1 h2 h3 h5

end Work.CORE4

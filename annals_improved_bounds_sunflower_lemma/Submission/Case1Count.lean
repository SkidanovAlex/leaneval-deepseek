import Mathlib
import Submission.FixedUDefs

open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- 4-part code of a case-1 pair (V,A): B0 = V ∪ χ(A,U), C, A, Q -/
structure Case1Code (α : Type*) where
  B0 : Finset α
  C : Finset α
  A : Finset α
  Q : Finset α
deriving DecidableEq

/-- code map of a pair -/
noncomputable def case1Code (S : Finset (Finset α)) (U : Finset α) (p : Finset α × Finset α) : Case1Code α :=
  { B0 := p.1 ∪ chi S U p.2,
    C := chi S U p.2 ∩ chi S U (remMin S U (p.1 ∪ chi S U p.2)),
    A := p.2,
    Q := p.1 ∩ chi S U p.2 }

lemma case1Code_injective {S : Finset (Finset α)} {U : Finset α} : Function.Injective (case1Code S U) := by
  intro p p' h
  rcases p with ⟨V, A⟩
  rcases p' with ⟨V', A'⟩
  simp [case1Code] at h
  rcases h with ⟨hB0, hC, hA, hQ⟩
  subst A'
  have hV : V = V' := by
    apply Finset.ext
    intro x
    by_cases hxR : x ∈ chi S U A
    · have h1 : x ∈ V ↔ x ∈ V ∩ chi S U A := by simp [hxR]
      have h2 : x ∈ V' ∩ chi S U A ↔ x ∈ V' := by simp [hxR]
      have h3 : x ∈ V ∩ chi S U A ↔ x ∈ V' ∩ chi S U A := by rw [hQ]
      exact h1.trans (h3.trans h2)
    · have h1 : x ∈ V ↔ x ∈ (V ∪ chi S U A) \ chi S U A := by
        rw [union_sdiff_right]
        simp [hxR]
      have h2 : x ∈ (V' ∪ chi S U A) \ chi S U A ↔ x ∈ V' := by
        rw [union_sdiff_right]
        simp [hxR]
      have h3 : x ∈ (V ∪ chi S U A) \ chi S U A ↔ x ∈ (V' ∪ chi S U A) \ chi S U A := by rw [hB0]
      exact h1.trans (h3.trans h2)
  subst V'
  rfl

/-- extract fiber membership facts -/
lemma mem_case1Fiber_facts {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α} {v k s t : ℕ} {r : ℝ}
    (h : (V,A) ∈ case1Fiber X S U v r k s t) :
    V ∈ cardSubsets (X \ U) v ∧ A ∈ S ∧ (chi S U A).card = s ∧
      (chi S (U ∪ V) A).card = t ∧ case1p S X U V A r k v := by
  classical
  simp [case1Fiber, pairSet] at h
  rcases h with ⟨hVhA, hs, ht, hc⟩
  rcases hVhA with ⟨hV, hA⟩
  exact ⟨hV, hA, hs, ht, hc⟩

/-- B0 := V ∪ χ(A,U) lies in bigB0 -/
lemma B0_mem_bigB0 {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α} {v k s t : ℕ} {r : ℝ}
    (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X)
    (h : (V,A) ∈ case1Fiber X S U v r k s t) :
    V ∪ chi S U A ∈ bigB0 X U v s := by
  classical
  have ⟨hV, hA, hs, ht, hc⟩ := mem_case1Fiber_facts (S:=S) h
  let R := chi S U A
  let B0 := V ∪ R
  have hRsub : R ⊆ X \ U := chi_subset_sdiff (S:=S) (X:=X) (U:=U) (A:=A) hA hU (hS A hA)
  have hB0sub : B0 ⊆ X \ U := by
    have hVsub : V ⊆ X \ U := (Finset.mem_powersetCard.mp hV).1
    exact union_subset hVsub hRsub
  have hv_le : v ≤ B0.card := by
    have hsub : V ⊆ B0 := by simp [B0]
    have hvc : v ≤ V.card := le_of_eq (Finset.mem_powersetCard.mp hV).2.symm
    exact le_trans hvc (Finset.card_le_card hsub)
  have hB0le : B0.card ≤ v + s := by
    have h1 : B0.card ≤ V.card + R.card := by simpa [B0] using (Finset.card_union_le (s := V) (t := R))
    have hvc : V.card = v := (Finset.mem_powersetCard.mp hV).2
    have hrc : R.card = s := hs
    simpa [hvc, hrc] using h1
  let j := B0.card - v
  have hjmem : j ∈ Finset.range (s+1) := by simp [j]; omega
  have hcardj : B0.card = v + j := by
    dsimp [j]
    exact (Nat.add_sub_of_le hv_le).symm
  have hmem : B0 ∈ cardSubsets (X \ U) (v + j) := by
    rw [← hcardj]
    exact Finset.mem_powersetCard.mpr ⟨hB0sub, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨j, hjmem, hmem⟩

/-- remMin facts for B0 := V ∪ χ(A,U) -/
lemma remMin_bounds {S : Finset (Finset α)} {U V A B0 : Finset α} {s : ℕ}
    (hA : A ∈ S) (hB0 : B0 = V ∪ chi S U A) (hs : (chi S U A).card = s) :
    remMin S U B0 ∈ S ∧ chi S U (remMin S U B0) ⊆ B0 ∧
      (chi S U (remMin S U B0)).card ≤ s := by
  have hR : chi S U A ⊆ B0 := by
    rw [hB0]
    exact Finset.subset_union_right
  exact ⟨remMin_mem_S (S:=S) (U:=U) (B0:=B0) (A:=A) hA hR,
    remMin_rem_subset (S:=S) (U:=U) (B0:=B0) (A:=A) hA hR,
    by simpa [hs] using remMin_rem_le (S:=S) (U:=U) (B0:=B0) (A:=A) hA hR⟩

/-- |C| ≥ t -/
lemma case1_C_card_ge {X : Finset α} {S : Finset (Finset α)} {U V A : Finset α} {v k s t : ℕ} {r : ℝ}
    (h : (V,A) ∈ case1Fiber X S U v r k s t) :
    t ≤ (chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A))).card := by
  classical
  have ⟨hV, hA, hs, ht, hc⟩ := mem_case1Fiber_facts (S:=S) h
  let B0 := V ∪ chi S U A
  let j := remMin S U B0
  let Bj := best S U j
  have hB0def : B0 = V ∪ chi S U A := rfl
  have hmemS : j ∈ S := (remMin_bounds (S:=S) (U:=U) (V:=V) (A:=A) (B0:=B0) (s:=s) hA hB0def hs).1
  have hsubRem : chi S U j ⊆ B0 := (remMin_bounds (S:=S) (U:=U) (V:=V) (A:=A) (B0:=B0) (s:=s) hA hB0def hs).2.1
  have hBjS : Bj ∈ S := best_mem (S:=S) (U:=U) (A:=j) hmemS
  have hBjU : Bj ⊆ U ∪ B0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.mem_union_left B0 hxU
    · have hxchi : x ∈ chi S U j := by
        change x ∈ best S U j \ U
        exact Finset.mem_sdiff.mpr ⟨hx, hxU⟩
      exact Finset.mem_union_right U (hsubRem hxchi)
  have hBjsub2 : Bj ⊆ A ∪ (U ∪ V) := by
    intro x hx
    have hxUV : x ∈ U ∪ B0 := hBjU hx
    rcases Finset.mem_union.mp hxUV with hxU | hxB0
    · exact Finset.mem_union_right A (Finset.mem_union_left V hxU)
    · have hxB0' : x ∈ V ∪ chi S U A := by simpa [B0] using hxB0
      rcases Finset.mem_union.mp hxB0' with hxV | hxR
      · exact Finset.mem_union_right A (Finset.mem_union_right U hxV)
      · exact Finset.mem_union_left (U ∪ V) (chi_subset (S:=S) (U:=U) (A:=A) hA hxR)
  have hle1 : (chi S (U ∪ V) A).card ≤ (Bj \ (U ∪ V)).card :=
    chi_card_le (S:=S) (U:=U ∪ V) (A:=A) (A':=Bj) hA hBjS hBjsub2
  have htle : t ≤ (Bj \ (U ∪ V)).card := by
    rw [ht] at hle1
    exact hle1
  have hset : Bj \ (U ∪ V) = (Bj \ U) \ V := by
    have h1 : (Bj \ U) \ V = (Bj \ U) ∩ (Bj \ V) := Finset.sdiff_sdiff_left' Bj U V
    have h2 : Bj \ (U ∪ V) = (Bj \ U) ∩ (Bj \ V) := by rw [Finset.sdiff_union_distrib]
    exact (h1.trans h2.symm).symm
  have hchi : chi S U j = Bj \ U := by
    dsimp [chi, Bj]
  have hsubRemV : chi S U j \ V ⊆ chi S U A ∩ chi S U j := by
    intro x hx
    have hxmem : x ∈ chi S U j := (Finset.mem_sdiff.mp hx).1
    have hxnV : x ∉ V := (Finset.mem_sdiff.mp hx).2
    have hxB0 : x ∈ B0 := hsubRem hxmem
    have hxB0' : x ∈ V ∪ chi S U A := by simpa [B0] using hxB0
    have hxA : x ∈ chi S U A := by
      rcases Finset.mem_union.mp hxB0' with hxV | hxR
      · exact False.elim (hxnV hxV)
      · exact hxR
    exact Finset.mem_inter.mpr ⟨hxA, hxmem⟩
  have hleC : (chi S U j \ V).card ≤ (chi S U A ∩ chi S U j).card :=
    Finset.card_le_card hsubRemV
  have hlen : (Bj \ (U ∪ V)).card = (chi S U j \ V).card := by
    rw [hset]
    rw [hchi]
  calc
    t ≤ (Bj \ (U ∪ V)).card := htle
    _ = (chi S U j \ V).card := hlen
    _ ≤ (chi S U A ∩ chi S U j).card := hleC
    _ = (chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A))).card := by
      dsimp [j, B0]

/-- generic: if every fiber over the image has real size ≤ c then #s ≤ #image * c -/
lemma real_card_le_image_mul {ι β : Type*} [DecidableEq β] (s : Finset ι) (f : ι → β) (c : ℝ)
    (h : ∀ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) ≤ c) :
    (s.card : ℝ) ≤ (s.image f).card * c := by
  classical
  have hEqN := Finset.card_eq_sum_card_image (f := f) (s := s)
  have hEq : (s.card : ℝ) = ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) := by
    exact_mod_cast hEqN
  calc
    (s.card : ℝ) = ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) := hEq
    _ ≤ ∑ b ∈ s.image f, c := Finset.sum_le_sum (fun b hb => h b hb)
    _ = (s.image f).card * c := by simp

/-- pick C t is a t-subset of C when t ≤ C.card -/
lemma pick_subset_card {C : Finset α} {t : ℕ} (h : t ≤ C.card) :
    pick C t ⊆ C ∧ (pick C t).card = t :=
  pick_spec (Finset.exists_subset_card_eq h)

/-- A ∈ τ(pick C t, B0, s) -/
lemma case1_A_mem_tau {S : Finset (Finset α)} {U V A B0 C : Finset α} {s t : ℕ}
    (hA : A ∈ S) (hB0 : B0 = V ∪ chi S U A)
    (hCsub : C ⊆ chi S U A) (hs : (chi S U A).card = s) (htC : t ≤ C.card) :
    A ∈ tau S U (pick C t) B0 s := by
  classical
  have hpick := pick_subset_card (C:=C) (t:=t) htC
  have hpickC : pick C t ⊆ chi S U A := subset_trans hpick.1 hCsub
  rw [tau]
  simp [hA, hpickC, hs]
  exact by simpa [hB0] using (Finset.subset_union_right (s₁ := V) (s₂ := chi S U A))

/-- |τ(pick C t) B0 s| ≤ φ(s,t) by case-1 hypothesis -/
lemma case1_tau_le {X : Finset α} {S : Finset (Finset α)} {U V A B0 C : Finset α} {v k s t : ℕ} {r : ℝ}
    (hc1 : case1p S X U V A r k v) (hB0 : B0 = V ∪ chi S U A)
    (hCsub : C ⊆ chi S U A) (hs : (chi S U A).card = s)
    (ht : (chi S (U ∪ V) A).card = t) (htC : t ≤ C.card) :
    ((tau S U (pick C t) B0 s).card : ℝ) ≤ phiVal r k X v s t := by
  classical
  have hpick := pick_subset_card (C:=C) (t:=t) htC
  have hpickC : pick C t ⊆ chi S U A := subset_trans hpick.1 hCsub
  have hcard : (pick C t).card = tVal S U V A := by
    rw [tVal]
    simpa [ht] using hpick.2
  have h := (hc1.2 (pick C t) hpickC hcard)
  simpa [hB0, hs, ht, tVal, sVal] using h

/-- all subsets of a set of size ≤ s: 2^card ≤ 2^s -/
lemma card_powerset_le_two_pow {R : Finset α} {s : ℕ} (h : R.card ≤ s) :
    ((R.powerset).card : ℝ) ≤ (2 : ℝ) ^ s := by
  have hc : R.powerset.card = 2 ^ R.card := Finset.card_powerset R
  have hle : 2 ^ R.card ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h
  rw [hc]
  exact_mod_cast hle

/-- φ ≥ 0 when r ≥ 1 -/
lemma phiVal_nonneg {X : Finset α} {v k s t : ℕ} {r : ℝ} (hr1 : 1 ≤ r) :
    0 ≤ phiVal r k X v s t := by
  unfold phiVal phi
  have hr0 : 0 ≤ r := by linarith
  have hn0 : 0 ≤ (X.card : ℝ) := by exact_mod_cast Nat.zero_le X.card
  have hv0 : 0 ≤ (v : ℝ) := by exact_mod_cast Nat.zero_le v
  have hrho0 : 0 ≤ (rho : ℝ) := by unfold rho; positivity
  have hden0 : 0 ≤ (((v : ℝ) * r / (X.card : ℝ)) ^ t) := by
    exact pow_nonneg (div_nonneg (mul_nonneg hv0 hr0) hn0) t
  have hbase0 : 0 ≤ (rho : ℝ) * (v : ℝ) / (X.card : ℝ) := div_nonneg (mul_nonneg hrho0 hv0) hn0
  have hnum0 : 0 ≤ (r ^ k) * (((rho : ℝ) * (v : ℝ) / (X.card : ℝ)) ^ s) := by
    exact mul_nonneg (pow_nonneg hr0 k) (pow_nonneg hbase0 s)
  exact div_nonneg hnum0 hden0

theorem case1Fiber_card_le {X : Finset α} {S : Finset (Finset α)} {U : Finset α}
    {v k s t : ℕ} {r : ℝ}
    (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X) (hUmem : ¬ ∃ A' ∈ S, A' ⊆ U)
    (hr1 : 1 ≤ r) (ht1 : 1 ≤ t) (hts : t ≤ s) :
    (((case1Fiber X S U v r k s t).card : ℝ) ≤
      (bigB0 X U v s).card * ((4 : ℝ) ^ s) * phiVal r k X v s t) := by
  classical
  let F : Finset (Finset α × Finset α) := case1Fiber X S U v r k s t
  let G : Finset (Finset α) := bigB0 X U v s
  let φ : ℝ := phiVal r k X v s t
  let M : Finset (Case1Code α) := F.image (fun p => case1Code S U p)
  let M3 : Finset (Finset α × Finset α × Finset α) := M.image (fun q => (q.B0, q.C, q.A))
  let M2 : Finset (Finset α × Finset α) := M3.image (fun r => (r.1, r.2.1))
  let M1 : Finset (Finset α) := M2.image (fun b => b.1)
  have hφ0 : 0 ≤ φ := by simpa [φ] using phiVal_nonneg (X:=X) (v:=v) (k:=k) (s:=s) (t:=t) hr1
  have htwo0 : 0 ≤ (2 : ℝ) ^ s := by positivity
  -- #F = #M by injectivity of the code
  have hEq : (F.card : ℝ) = (M.card : ℝ) := by
    have hinj : Set.InjOn (case1Code S U) (↑F : Set (Finset α × Finset α)) :=
      case1Code_injective.injOn
    have hc : M.card = F.card := by
      dsimp [M]
      simpa using (Finset.card_image_of_injOn hinj)
    exact_mod_cast hc.symm
  -- LAYER 1: M - M3, fibers over r=(B0,C,A) have size ≤ 2^s (choices of Q)
  have h1 : ∀ r ∈ M3, ((M.filter (fun q => (q.B0, q.C, q.A) = r)).card : ℝ) ≤ (2 : ℝ) ^ s := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨q₀, hq₀M, hq₀eq⟩
    rcases Finset.mem_image.mp hq₀M with ⟨p₀, hp₀F, hcode₀⟩
    rcases p₀ with ⟨V₀, A₀⟩
    have ⟨_, hA₀mem, hs₀, _, _⟩ := mem_case1Fiber_facts (S:=S) hp₀F
    have hq₀A : q₀.A = A₀ := by
      have h := congrArg Case1Code.A hcode₀.symm
      simpa [case1Code] using h
    let fiber : Finset (Case1Code α) := M.filter (fun q => (q.B0, q.C, q.A) = r)
    have hQsub : ∀ q ∈ fiber, q.Q ⊆ chi S U A₀ := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqM, hqeq⟩
      rcases Finset.mem_image.mp hqM with ⟨p, hpF, hcode⟩
      rcases p with ⟨V, A⟩
      have hqA : q.A = A := by
        have h := congrArg Case1Code.A hcode.symm
        simpa [case1Code] using h
      have hAeq : A = A₀ := by
        have h1 : q.A = r.2.2 := by
          exact congrArg (fun z : Finset α × Finset α × Finset α => z.2.2) hqeq
        have h2 : q₀.A = r.2.2 := by
          exact congrArg (fun z : Finset α × Finset α × Finset α => z.2.2) hq₀eq
        calc
          A = q.A := hqA.symm
          _ = r.2.2 := h1
          _ = q₀.A := h2.symm
          _ = A₀ := hq₀A
      have hQ : q.Q ⊆ chi S U A := by
        rw [← hcode]
        simp [case1Code]
      simpa [hAeq] using hQ
    have hmaps : Set.MapsTo (fun q : Case1Code α => q.Q) (↑fiber : Set (Case1Code α))
        (↑((chi S U A₀).powerset) : Set (Finset α)) := by
      intro q hq
      exact Finset.mem_powerset.mpr (hQsub q hq)
    have hinj : Set.InjOn (fun q : Case1Code α => q.Q) (↑fiber : Set (Case1Code α)) := by
      intro q₁ hq₁ q₂ hq₂ hQeq
      cases q₁ with
      | mk B0₁ C₁ A₁ Q₁ =>
        cases q₂ with
        | mk B0₂ C₂ A₂ Q₂ =>
          have hB1 : B0₁ = r.1 := by
            exact congrArg (fun z : Finset α × Finset α × Finset α => z.1) (Finset.mem_filter.mp hq₁).2
          have hB2 : B0₂ = r.1 := by
            exact congrArg (fun z : Finset α × Finset α × Finset α => z.1) (Finset.mem_filter.mp hq₂).2
          have hC1 : C₁ = r.2.1 := by
            exact congrArg (fun z : Finset α × Finset α × Finset α => z.2.1) (Finset.mem_filter.mp hq₁).2
          have hC2 : C₂ = r.2.1 := by
            exact congrArg (fun z : Finset α × Finset α × Finset α => z.2.1) (Finset.mem_filter.mp hq₂).2
          have hA1 : A₁ = r.2.2 := by
            exact congrArg (fun z : Finset α × Finset α × Finset α => z.2.2) (Finset.mem_filter.mp hq₁).2
          have hA2 : A₂ = r.2.2 := by
            exact congrArg (fun z : Finset α × Finset α × Finset α => z.2.2) (Finset.mem_filter.mp hq₂).2
          have hB : B0₁ = B0₂ := hB1.trans hB2.symm
          have hC : C₁ = C₂ := hC1.trans hC2.symm
          have hA : A₁ = A₂ := hA1.trans hA2.symm
          have hQ : Q₁ = Q₂ := by simpa using hQeq
          rw [hB, hC, hA, hQ]
    have hcardle : fiber.card ≤ (chi S U A₀).powerset.card := by
      exact Finset.card_le_card_of_injOn (fun q : Case1Code α => q.Q) hmaps hinj
    have hcardReal : (fiber.card : ℝ) ≤ (2 : ℝ) ^ s := by
      have h1n : (fiber.card : ℝ) ≤ ((chi S U A₀).powerset.card : ℝ) := by exact_mod_cast hcardle
      exact le_trans h1n (card_powerset_le_two_pow (le_of_eq hs₀))
    simpa [fiber] using hcardReal
  -- apply layer lemma
  have hM_le : (M.card : ℝ) ≤ (M3.card : ℝ) * (2 : ℝ) ^ s := by
    simpa [M3] using real_card_le_image_mul M (fun q => (q.B0, q.C, q.A)) ((2 : ℝ) ^ s) h1
  -- LAYER 2: M3 - M2, fibers over b=(B0,C) have size ≤ φ (choices of A)
  have h2 : ∀ b ∈ M2, ((M3.filter (fun r => (r.1, r.2.1) = b)).card : ℝ) ≤ φ := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨r₀, hr₀M3, hr₀eq⟩
    rcases Finset.mem_image.mp hr₀M3 with ⟨q₀, hq₀M, hq₀eq⟩
    rcases Finset.mem_image.mp hq₀M with ⟨p₀, hp₀F, hcode₀⟩
    rcases p₀ with ⟨V₀, A₀⟩
    have ⟨_, hA₀mem, hs₀, ht₀, hc₀⟩ := mem_case1Fiber_facts (S:=S) hp₀F
    have hbB₀ : b.1 = V₀ ∪ chi S U A₀ := by
      calc
        b.1 = r₀.1 := (congrArg (fun z : Finset α × Finset α => z.1) hr₀eq).symm
        _ = q₀.B0 := (congrArg (fun z : Finset α × Finset α × Finset α => z.1) hq₀eq).symm
        _ = V₀ ∪ chi S U A₀ := by
          have h := congrArg Case1Code.B0 hcode₀.symm
          simpa [case1Code] using h
    have hbC₀ : b.2 = chi S U A₀ ∩ chi S U (remMin S U (V₀ ∪ chi S U A₀)) := by
      calc
        b.2 = r₀.2.1 := (congrArg (fun z : Finset α × Finset α => z.2) hr₀eq).symm
        _ = q₀.C := (congrArg (fun z : Finset α × Finset α × Finset α => z.2.1) hq₀eq).symm
        _ = chi S U A₀ ∩ chi S U (remMin S U (V₀ ∪ chi S U A₀)) := by
          have h := congrArg Case1Code.C hcode₀.symm
          simpa [case1Code] using h
    have hC₀sub : b.2 ⊆ chi S U A₀ := by
      rw [hbC₀]
      exact Finset.inter_subset_left
    have htC₀ : t ≤ b.2.card := by
      have h := case1_C_card_ge (S:=S) hp₀F
      rwa [← hbC₀] at h
    let tset : Finset (Finset α) := tau S U (pick (b.2) t) (b.1) s
    have hτle : (tset.card : ℝ) ≤ φ := by
      have h := case1_tau_le (S:=S) (X:=X) (U:=U) (V:=V₀) (A:=A₀) (B0:=b.1) (C:=b.2)
        hc₀ hbB₀ hC₀sub hs₀ ht₀ htC₀
      simpa [tset, φ] using h
    let fiber := M3.filter (fun r => (r.1, r.2.1) = b)
    have hAmem : ∀ r ∈ fiber, r.2.2 ∈ tset := by
      intro r hr
      rcases Finset.mem_filter.mp hr with ⟨hrM3, hreq⟩
      rcases Finset.mem_image.mp hrM3 with ⟨q, hqM, hqeq⟩
      rcases Finset.mem_image.mp hqM with ⟨p, hpF, hcode⟩
      rcases p with ⟨V, A⟩
      have ⟨_, hAmemS, hsA, _, _⟩ := mem_case1Fiber_facts (S:=S) hpF
      have hb1 : b.1 = r.1 := (congrArg (fun z : Finset α × Finset α => z.1) hreq).symm
      have hb2 : b.2 = r.2.1 := (congrArg (fun z : Finset α × Finset α => z.2) hreq).symm
      have hBp : r.1 = V ∪ chi S U A := by
        calc
          r.1 = q.B0 := (congrArg (fun z : Finset α × Finset α × Finset α => z.1) hqeq).symm
          _ = V ∪ chi S U A := by
            have h := congrArg Case1Code.B0 hcode.symm
            simpa [case1Code] using h
      have hCp : r.2.1 = chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A)) := by
        calc
          r.2.1 = q.C := (congrArg (fun z : Finset α × Finset α × Finset α => z.2.1) hqeq).symm
          _ = chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A)) := by
            have h := congrArg Case1Code.C hcode.symm
            simpa [case1Code] using h
      have hAval : r.2.2 = A := by
        calc
          r.2.2 = q.A := (congrArg (fun z : Finset α × Finset α × Finset α => z.2.2) hqeq).symm
          _ = A := by
            have h := congrArg Case1Code.A hcode.symm
            simpa [case1Code] using h
      have hsubC : b.2 ⊆ chi S U A := by
        rw [hb2, hCp]
        exact Finset.inter_subset_left
      have hB0eq : b.1 = V ∪ chi S U A := by
        rw [hb1, hBp]
      have htC : t ≤ b.2.card := by
        have h := case1_C_card_ge (S:=S) hpF
        rw [hCp.symm, hb2.symm] at h
        exact h
      have hmem := case1_A_mem_tau (S:=S) (U:=U) (V:=V) (A:=A) (B0:=b.1) (C:=b.2)
        hAmemS hB0eq hsubC hsA htC
      rw [hAval]
      simpa [tset] using hmem
    have hinj : Set.InjOn (fun r : Finset α × Finset α × Finset α => r.2.2) (↑fiber : Set _) := by
      intro r₁ hr₁ r₂ hr₂ hAeq
      have h₁ : (r₁.1, r₁.2.1) = b := (Finset.mem_filter.mp hr₁).2
      have h₂ : (r₂.1, r₂.2.1) = b := (Finset.mem_filter.mp hr₂).2
      apply Prod.ext
      · have hB1 : r₁.1 = b.1 := congrArg (fun z : Finset α × Finset α => z.1) h₁
        have hB2 : r₂.1 = b.1 := congrArg (fun z : Finset α × Finset α => z.1) h₂
        exact hB1.trans hB2.symm
      · apply Prod.ext
        · have hC1 : r₁.2.1 = b.2 := congrArg (fun z : Finset α × Finset α => z.2) h₁
          have hC2 : r₂.2.1 = b.2 := congrArg (fun z : Finset α × Finset α => z.2) h₂
          exact hC1.trans hC2.symm
        · exact hAeq
    have hAset_sub : fiber.image (fun r : Finset α × Finset α × Finset α => r.2.2) ⊆ tset := by
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨r, hr, rfl⟩
      exact hAmem r hr
    have hcardle : fiber.card ≤ tset.card := by
      calc
        fiber.card = (fiber.image (fun r : Finset α × Finset α × Finset α => r.2.2)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ tset.card := Finset.card_le_card hAset_sub
    have hcardReal : (fiber.card : ℝ) ≤ φ := by
      have h1n : (fiber.card : ℝ) ≤ (tset.card : ℝ) := by exact_mod_cast hcardle
      exact le_trans h1n hτle
    simpa [fiber] using hcardReal
  -- apply layer lemma
  have hM3_le : (M3.card : ℝ) ≤ (M2.card : ℝ) * φ := by
    simpa [M2, φ] using real_card_le_image_mul M3 (fun r => (r.1, r.2.1)) φ h2
  -- LAYER 3: M2 - M1, fibers over B0 have size ≤ 2^s (choices of C)
  have h3 : ∀ B0 ∈ M1, ((M2.filter (fun b => b.1 = B0)).card : ℝ) ≤ (2 : ℝ) ^ s := by
    intro B0 hB0
    rcases Finset.mem_image.mp hB0 with ⟨b₀, hb₀M2, hb₀eq⟩
    rcases Finset.mem_image.mp hb₀M2 with ⟨r₀, hr₀M3, hr₀eq⟩
    rcases Finset.mem_image.mp hr₀M3 with ⟨q₀, hq₀M, hq₀eq⟩
    rcases Finset.mem_image.mp hq₀M with ⟨p₀, hp₀F, hcode₀⟩
    rcases p₀ with ⟨V₀, A₀⟩
    have ⟨_, hA₀mem, hs₀, _, _⟩ := mem_case1Fiber_facts (S:=S) hp₀F
    have hB₀val : B0 = V₀ ∪ chi S U A₀ := by
      calc
        B0 = b₀.1 := hb₀eq.symm
        _ = r₀.1 := (congrArg (fun z : Finset α × Finset α => z.1) hr₀eq).symm
        _ = q₀.B0 := (congrArg (fun z : Finset α × Finset α × Finset α => z.1) hq₀eq).symm
        _ = V₀ ∪ chi S U A₀ := by
          have h := congrArg Case1Code.B0 hcode₀.symm
          simpa [case1Code] using h
    have hjr : (chi S U (remMin S U B0)).card ≤ s :=
      (remMin_bounds (S:=S) (U:=U) (V:=V₀) (A:=A₀) (B0:=B0) (s:=s) hA₀mem hB₀val hs₀).2.2
    let fiber := M2.filter (fun b => b.1 = B0)
    have hCsub : ∀ b ∈ fiber, b.2 ⊆ chi S U (remMin S U B0) := by
      intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hbM2, hbB⟩
      rcases Finset.mem_image.mp hbM2 with ⟨r, hrM3, hreq⟩
      rcases Finset.mem_image.mp hrM3 with ⟨q, hqM, hqeq⟩
      rcases Finset.mem_image.mp hqM with ⟨p, hpF, hcode⟩
      rcases p with ⟨V, A⟩
      have hBp : r.1 = V ∪ chi S U A := by
        calc
          r.1 = q.B0 := (congrArg (fun z : Finset α × Finset α × Finset α => z.1) hqeq).symm
          _ = V ∪ chi S U A := by
            have h := congrArg Case1Code.B0 hcode.symm
            simpa [case1Code] using h
      have hCp : r.2.1 = chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A)) := by
        calc
          r.2.1 = q.C := (congrArg (fun z : Finset α × Finset α × Finset α => z.2.1) hqeq).symm
          _ = chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A)) := by
            have h := congrArg Case1Code.C hcode.symm
            simpa [case1Code] using h
      have hb1' : b.1 = r.1 := (congrArg (fun z : Finset α × Finset α => z.1) hreq).symm
      have hb2' : b.2 = r.2.1 := (congrArg (fun z : Finset α × Finset α => z.2) hreq).symm
      have hB0p : V ∪ chi S U A = B0 := by
        rw [← hBp]
        exact hb1'.symm.trans hbB
      rw [hb2', hCp]
      -- chi S U A ∩ chi S U (remMin S U (V ∪ chi S U A)) ⊆ chi S U (remMin S U B0)
      have hrem : remMin S U (V ∪ chi S U A) = remMin S U B0 := by rw [hB0p]
      rw [hrem]
      exact Finset.inter_subset_right
    have hmaps : Set.MapsTo (fun b : Finset α × Finset α => b.2) (↑fiber : Set _)
        (↑((chi S U (remMin S U B0)).powerset) : Set (Finset α)) := by
      intro b hb
      exact Finset.mem_powerset.mpr (hCsub b hb)
    have hinj : Set.InjOn (fun b : Finset α × Finset α => b.2) (↑fiber : Set _) := by
      intro b₁ hb₁ b₂ hb₂ hCeq
      apply Prod.ext
      · have h1 : b₁.1 = B0 := (Finset.mem_filter.mp hb₁).2
        have h2 : b₂.1 = B0 := (Finset.mem_filter.mp hb₂).2
        exact h1.trans h2.symm
      · exact hCeq
    have hcardle : fiber.card ≤ (chi S U (remMin S U B0)).powerset.card := by
      exact Finset.card_le_card_of_injOn (fun b : Finset α × Finset α => b.2) hmaps hinj
    have hcardReal : (fiber.card : ℝ) ≤ (2 : ℝ) ^ s := by
      have h1n : (fiber.card : ℝ) ≤ (((chi S U (remMin S U B0)).powerset).card : ℝ) := by exact_mod_cast hcardle
      exact le_trans h1n (card_powerset_le_two_pow hjr)
    simpa [fiber] using hcardReal
  have hM2_le : (M2.card : ℝ) ≤ (M1.card : ℝ) * (2 : ℝ) ^ s := by
    simpa [M1] using real_card_le_image_mul M2 (fun b => b.1) ((2 : ℝ) ^ s) h3
  -- LAYER 4: M1 ⊆ G
  have hM1_sub : M1 ⊆ G := by
    intro B0 hB0
    rcases Finset.mem_image.mp hB0 with ⟨b₀, hb₀M2, hb₀eq⟩
    rcases Finset.mem_image.mp hb₀M2 with ⟨r₀, hr₀M3, hr₀eq⟩
    rcases Finset.mem_image.mp hr₀M3 with ⟨q₀, hq₀M, hq₀eq⟩
    rcases Finset.mem_image.mp hq₀M with ⟨p₀, hp₀F, hcode₀⟩
    rcases p₀ with ⟨V₀, A₀⟩
    have hmem : V₀ ∪ chi S U A₀ ∈ G := by
      simpa [G] using B0_mem_bigB0 (X:=X) (S:=S) (U:=U) (V:=V₀) (A:=A₀) (v:=v) (k:=k) (s:=s) (t:=t) hU hS hp₀F
    have hBval : B0 = V₀ ∪ chi S U A₀ := by
      calc
        B0 = b₀.1 := hb₀eq.symm
        _ = r₀.1 := (congrArg (fun z : Finset α × Finset α => z.1) hr₀eq).symm
        _ = q₀.B0 := (congrArg (fun z : Finset α × Finset α × Finset α => z.1) hq₀eq).symm
        _ = V₀ ∪ chi S U A₀ := by
          have h := congrArg Case1Code.B0 hcode₀.symm
          simpa [case1Code] using h
    simpa [hBval] using hmem
  have hM1_le : (M1.card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hM1_sub)
  -- FINAL CHAIN
  calc
    (F.card : ℝ) = (M.card : ℝ) := hEq
    _ ≤ (M3.card : ℝ) * (2 : ℝ) ^ s := hM_le
    _ ≤ ((M2.card : ℝ) * φ) * (2 : ℝ) ^ s := by
      exact mul_le_mul_of_nonneg_right hM3_le htwo0
    _ ≤ (((M1.card : ℝ) * (2 : ℝ) ^ s) * φ) * (2 : ℝ) ^ s := by
      have hm1 : (M2.card : ℝ) * φ ≤ ((M1.card : ℝ) * (2 : ℝ) ^ s) * φ :=
        mul_le_mul_of_nonneg_right hM2_le hφ0
      exact mul_le_mul_of_nonneg_right hm1 htwo0
    _ ≤ (((G.card : ℝ) * (2 : ℝ) ^ s) * φ) * (2 : ℝ) ^ s := by
      have hm1 : ((M1.card : ℝ) * (2 : ℝ) ^ s) * φ ≤ ((G.card : ℝ) * (2 : ℝ) ^ s) * φ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM1_le htwo0) hφ0
      exact mul_le_mul_of_nonneg_right hm1 htwo0
    _ = (G.card : ℝ) * (4 : ℝ) ^ s * φ := by
      have hm : (2 : ℝ) ^ s * (2 : ℝ) ^ s = (4 : ℝ) ^ s := by
        rw [← mul_pow]
        norm_num
      calc
        (((G.card : ℝ) * (2 : ℝ) ^ s) * φ) * (2 : ℝ) ^ s
            = (G.card : ℝ) * ((2 : ℝ) ^ s * (2 : ℝ) ^ s) * φ := by ring
        _ = (G.card : ℝ) * (4 : ℝ) ^ s * φ := by rw [hm]

end Submission.Sun

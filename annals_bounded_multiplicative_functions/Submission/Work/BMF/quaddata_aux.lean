import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.quaddata_core
import Submission.Work.BMF.poly_growth
import Submission.Work.BMF.fam_card_le
import Submission.Work.BMF.prime_card_le
import Submission.Work.BMF.sigma_filter_sq
import Submission.Work.BMF.edge_count_core
import Submission.Work.BMF.incPairs_two_primes_forbidden
import Submission.Work.BMF.qd_pi0_ge_of_big
import Submission.Work.BMF.qd_qk_bound
import Submission.Work.BMF.qd_edge_lower
import Submission.Work.BMF.qd_small_c_modulus
import Submission.Work.BMF.qd_pi0_half
import Submission.Work.BMF.qd_pi0_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 8000000

namespace Work.BMF
open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

noncomputable def qdc (c₀ Cπ : ℝ) : ℝ :=
  min c₀ (min (5 * c₀ ^ 6 / (2 * Cπ ^ 2)) (200 * c₀ ^ 6 / Cπ ^ 3))

noncomputable def qdP₀ (c₀ Cπ P₀π : ℝ) : ℝ :=
  max P₀π (max ((2 * Cπ / (10 * c₀ ^ 3) + 2) ^ 2) 100)

noncomputable def qdCone (k : ℕ) (Cᵢ : ℝ) : ℝ := transConst k Cᵢ Cᵢ

noncomputable def qdC (k : ℕ) (Cᵢ : ℝ) : ℝ :=
  transConst k (symmConst k (qdCone k Cᵢ)) (qdCone k Cᵢ) + 1

theorem quaddata_aux (k : ℕ) (hk : 1 ≤ k) (c₀ Cᵢ : ℝ) (hc₀ : 0 < c₀) (hCᵢ : 0 < Cᵢ)
    (Cπ P₀π : ℝ) (hCπ : 0 < Cπ) (hP₀π : 0 < P₀π)
    (hprime : ∀ a b : ℝ, P₀π ≤ a → a ≤ b → b ≤ 7 * a / 5 →
      ((primesIn a b).card : ℝ) ≤ Cπ * pi0 a)
    (P₀ c C : ℝ) (hP₀π' : P₀π ≤ P₀) (hP₀big : (2 * Cπ / (10 * c₀ ^ 3) + 2) ^ 2 ≤ P₀)
    (hP₀4 : 4 ≤ P₀)
    (hc : 0 < c) (hcc : c ≤ c₀) (hc1 : c ≤ 5 * c₀ ^ 6 / (2 * Cπ ^ 2)) (hc2 : c ≤ 200 * c₀ ^ 6 / Cπ ^ 3)
    (hC : transConst k (symmConst k (qdCone k Cᵢ)) (qdCone k Cᵢ) ≤ C)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (X H a₁ b₁ a₂ b₂ c₁ c₂ : ℝ)
    (F₀ : PhaseFamily k f c₀ X H) (F₁ : PhaseFamily k f c₁ (X / a₁) (H / a₁))
    (F₂ : PhaseFamily k f c₂ (X / (a₁ * a₂)) (H / (a₁ * a₂)))
    (hcc₁ : c₀ ≤ c₁) (hcc₂ : c₀ ≤ c₂) (hP₀a₁ : P₀ ≤ a₁) (ha₁b₁ : a₁ ≤ b₁) (hn₁ : 5 * b₁ ≤ 7 * a₁)
    (hP₀a₂ : P₀ ≤ a₂) (ha₂b₂ : a₂ ≤ b₂) (hn₂ : 5 * b₂ ≤ 7 * a₂)
    (hXH : 200 * b₁ ^ 2 ≤ X / H) (hX : 0 < X)
    (hind₁ : ∀ x' ∈ F₁.fam, c₀ * pi0 a₁ ≤
      ((incPairs k Cᵢ F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol (F₁.pol x') x').card : ℝ))
    (hind₂ : ∀ x'' ∈ F₂.fam, c₀ * pi0 a₂ ≤
      ((incPairs k Cᵢ F₁.fam a₂ b₂ (H / a₁) (3 * H / (a₁ * a₂)) (H / (a₁ * a₂))
        F₁.pol (F₂.pol x'') x'').card : ℝ)) :
    ∃ P₁ P₂ : ℝ, P₁ * P₂ = a₁ * a₂ ∧ b₁ / 2 ≤ P₁ ∧ P₁ ≤ a₁ ∧ b₂ ≤ P₂ ∧ P₂ ≤ 2 * a₂ ∧
      Nonempty (QuadData k f c C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂) := by
  classical
  -- ================= basic positivity =================
  have hP₀pos : 0 < P₀ := lt_of_lt_of_le hP₀π hP₀π'
  have ha₁ : 0 < a₁ := lt_of_lt_of_le hP₀pos hP₀a₁
  have ha₂ : 0 < a₂ := lt_of_lt_of_le hP₀pos hP₀a₂
  have hb₁ : 0 < b₁ := lt_of_lt_of_le ha₁ ha₁b₁
  have hb₂ : 0 < b₂ := lt_of_lt_of_le ha₂ ha₂b₂
  have hXH0 : 0 < X / H := lt_of_lt_of_le (by positivity) hXH
  have hH : 0 < H := by
    rcases lt_trichotomy H 0 with h | h | h
    · exact absurd hXH0 (not_lt.mpr (le_of_lt (div_neg_of_pos_of_neg hX h)))
    · subst h; simp at hXH0
    · exact h
  have hb₁b₂ : b₁ * b₂ ≤ 2 * (a₁ * a₂) := by
    have h1 : b₁ ≤ 7 * a₁ / 5 := by linarith
    have h2 : b₂ ≤ 7 * a₂ / 5 := by linarith
    nlinarith [h1, h2, ha₁, ha₂, hb₁, hb₂]
  -- ================= definitions =================
  let Pr₁ : Finset ℕ := primesIn a₁ b₁
  let Pr₂ : Finset ℕ := primesIn a₂ b₂
  let Ainc : ℝ → Finset (ℝ × ℕ) :=
    fun x' => incPairs k Cᵢ F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol (F₁.pol x') x'
  let Binc : ℝ → Finset (ℝ × ℕ) :=
    fun x'' => incPairs k Cᵢ F₁.fam a₂ b₂ (H / a₁) (3 * H / (a₁ * a₂)) (H / (a₁ * a₂))
      F₁.pol (F₂.pol x'') x''
  let L₁ : ℝ := H / a₁
  let L₂ : ℝ := H / (a₁ * a₂)
  let M : ℝ := X / H
  have hL₁v : L₁ = H / a₁ := rfl
  have hL₂v : L₂ = H / (a₁ * a₂) := rfl
  have hL₁pos : 0 < L₁ := div_pos hH ha₁
  have hL₂pos : 0 < L₂ := div_pos hH (mul_pos ha₁ ha₂)
  have hMpos : 0 < M := hXH0
  have hβ₁ : ∀ x' ∈ F₁.fam, c₀ * pi0 a₁ ≤ ((Ainc x').card : ℝ) := by
    intro x' hx'; exact hind₁ x' hx'
  have hβ₂ : ∀ x'' ∈ F₂.fam, c₀ * pi0 a₂ ≤ ((Binc x'').card : ℝ) := by
    intro x'' hx''; exact hind₂ x'' hx''
  -- ================= the good prime sets =================
  let G : (ℝ × ℕ) → Finset ℕ := fun kk => Pr₁.filter (fun p' =>
    ∃ x' ∈ F₁.fam, (kk.1, p') ∈ Ainc x' ∧ ∃ x'' ∈ F₂.fam, (x', kk.2) ∈ Binc x'')
  have mem_G : ∀ (kk : ℝ × ℕ) (p' : ℕ), p' ∈ G kk ↔
      (∃ x' ∈ F₁.fam, (kk.1, p') ∈ Ainc x' ∧ ∃ x'' ∈ F₂.fam, (x', kk.2) ∈ Binc x'') := by
    intro kk p'
    simp only [G, Finset.mem_filter]
    constructor
    · intro h; exact h.2
    · intro h
      refine ⟨?_, h⟩
      obtain ⟨x', hx', h1, h2⟩ := h
      exact (Finset.mem_product.mp (Finset.mem_filter.mp h1).1).2
  let KF : Finset (ℝ × ℕ) := F₀.fam ×ˢ Pr₂
  let DOM : Finset ((ℝ × ℕ) × (ℕ × ℕ)) := KF.biUnion (fun kk =>
    (((G kk).product (G kk)).filter (fun q => q.1 ≠ q.2)).image (fun q => (kk, q)))
  have mem_DOM : ∀ z : (ℝ × ℕ) × (ℕ × ℕ), z ∈ DOM ↔
      z.1 ∈ KF ∧ z.2.1 ∈ G z.1 ∧ z.2.2 ∈ G z.1 ∧ z.2.1 ≠ z.2.2 := by
    intro z
    constructor
    · intro h
      simp only [DOM, Finset.mem_biUnion, Finset.mem_image] at h
      obtain ⟨kk, hkk, q, hq, hqeq⟩ := h
      obtain ⟨hqp, hne⟩ := Finset.mem_filter.mp hq
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hqp
      rw [← hqeq]
      exact ⟨hkk, h1, h2, hne⟩
    · rintro ⟨hkk, h1, h2, hne⟩
      simp only [DOM, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨z.1, hkk, z.2, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hne⟩, rfl⟩
  have hwit : ∀ (kk : ℝ × ℕ) (p' : ℕ), p' ∈ G kk → ∃ z : ℝ × ℝ, z.1 ∈ F₁.fam ∧
      (kk.1, p') ∈ Ainc z.1 ∧ z.2 ∈ F₂.fam ∧ (z.1, kk.2) ∈ Binc z.2 := by
    intro kk p' hp'
    obtain ⟨x', hx', h1, x'', hx'', h2⟩ := (mem_G kk p').mp hp'
    exact ⟨(x', x''), hx', h1, hx'', h2⟩
  let wit : (ℝ × ℕ) → ℕ → ℝ × ℝ := fun kk p' =>
    if h : ∃ z : ℝ × ℝ, z.1 ∈ F₁.fam ∧ (kk.1, p') ∈ Ainc z.1 ∧ z.2 ∈ F₂.fam ∧ (z.1, kk.2) ∈ Binc z.2
    then Classical.choose h else (0, 0)
  have wit_spec : ∀ (kk : ℝ × ℕ) (p' : ℕ), p' ∈ G kk → (wit kk p').1 ∈ F₁.fam ∧
      (kk.1, p') ∈ Ainc (wit kk p').1 ∧ (wit kk p').2 ∈ F₂.fam ∧
      ((wit kk p').1, kk.2) ∈ Binc (wit kk p').2 := by
    intro kk p' hp'
    have h := hwit kk p' hp'
    dsimp only [wit]
    rw [dif_pos h]
    exact Classical.choose_spec h
  let ed : (ℝ × ℕ) × (ℕ × ℕ) → Edge := fun q =>
    ⟨(wit q.1 q.2.1).2, (wit q.1 q.2.2).2, q.2.1, q.2.2⟩

  -- ================= positivity of pi0 =================
  have ha₁1 : (1:ℝ) < a₁ := lt_of_lt_of_le (by norm_num) (le_trans hP₀4 hP₀a₁)
  have ha₂1 : (1:ℝ) < a₂ := lt_of_lt_of_le (by norm_num) (le_trans hP₀4 hP₀a₂)
  have hb₂1 : (1:ℝ) < b₂ := lt_of_lt_of_le ha₂1 ha₂b₂
  have hπ₁pos : 0 < pi0 a₁ := div_pos ha₁ (Real.log_pos ha₁1)
  have hπ₂pos : 0 < pi0 a₂ := div_pos ha₂ (Real.log_pos ha₂1)
  -- ================= the domain of quintuplets =================
  let Qdom : Finset (Σ x'' : ℝ, Σ xp' : ℝ × ℕ, ℝ × ℕ) :=
    F₂.fam.sigma (fun x'' => (Binc x'').sigma (fun xp' => Ainc xp'.1))
  have hQdom_card : (Qdom.card : ℝ) =
      ∑ x'' ∈ F₂.fam, ∑ xp' ∈ Binc x'', ((Ainc xp'.1).card : ℝ) := by
    have e1 : Qdom.card = ∑ x'' ∈ F₂.fam, ((Binc x'').sigma (fun xp' => Ainc xp'.1)).card := by
      dsimp only [Qdom]
      exact Finset.card_sigma F₂.fam (fun x'' => (Binc x'').sigma (fun xp' => Ainc xp'.1))
    have e2 : ∀ x'' ∈ F₂.fam, ((Binc x'').sigma (fun xp' => Ainc xp'.1)).card
        = ∑ xp' ∈ Binc x'', (Ainc xp'.1).card := fun x'' _ => Finset.card_sigma (Binc x'') (fun xp' => Ainc xp'.1)
    rw [e1, Finset.sum_congr rfl e2]
    push_cast
    rfl
  have hQdom_ge : c₀ * pi0 a₁ * (c₀ * pi0 a₂) * (c₂ * M) ≤ (Qdom.card : ℝ) := by
    rw [hQdom_card]
    have h2 : ∀ x'' ∈ F₂.fam,
        (c₀ * pi0 a₂) * (c₀ * pi0 a₁) ≤ ∑ xp' ∈ Binc x'', ((Ainc xp'.1).card : ℝ) := by
      intro x'' hx''
      calc (c₀ * pi0 a₂) * (c₀ * pi0 a₁)
          ≤ (Binc x'').card * (c₀ * pi0 a₁) :=
            mul_le_mul_of_nonneg_right (hβ₂ x'' hx'') (by positivity)
        _ = ∑ xp' ∈ Binc x'', (c₀ * pi0 a₁) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ xp' ∈ Binc x'', ((Ainc xp'.1).card : ℝ) := by
            refine Finset.sum_le_sum (fun xp' hxp' => ?_)
            exact hβ₁ xp'.1 (Finset.mem_product.mp (Finset.mem_filter.mp hxp').1).1
    calc ∑ x'' ∈ F₂.fam, ∑ xp' ∈ Binc x'', ((Ainc xp'.1).card : ℝ)
        ≥ ∑ x'' ∈ F₂.fam, (c₀ * pi0 a₂) * (c₀ * pi0 a₁) := Finset.sum_le_sum h2
      _ = (F₂.fam.card : ℝ) * ((c₀ * pi0 a₂) * (c₀ * pi0 a₁)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≥ c₀ * pi0 a₁ * (c₀ * pi0 a₂) * (c₂ * M) := by
            have hMval : M = X / H := rfl
            have hcg := F₂.card_ge
            have hXHL : (X / (a₁ * a₂)) / (H / (a₁ * a₂)) = M := by
              rw [hMval]; field_simp
            rw [hXHL] at hcg
            calc c₀ * pi0 a₁ * (c₀ * pi0 a₂) * (c₂ * M)
                = (c₂ * M) * ((c₀ * pi0 a₂) * (c₀ * pi0 a₁)) := by ring
              _ ≤ (F₂.fam.card : ℝ) * ((c₀ * pi0 a₂) * (c₀ * pi0 a₁)) :=
                  mul_le_mul_of_nonneg_right hcg (by positivity)
  -- ================= the good-prime sum =================
  let φ : (Σ x'' : ℝ, Σ xp' : ℝ × ℕ, ℝ × ℕ) → (ℝ × ℕ) × ℕ :=
    fun t => ((t.2.2.1, t.2.1.2), t.2.2.2)
  let GS : Finset ((ℝ × ℕ) × ℕ) := KF.biUnion (fun kk => (G kk).image (fun p' => (kk, p')))
  have hGS_card : (GS.card : ℝ) = ∑ kk ∈ KF, ((G kk).card : ℝ) := by
    have e1 : GS.card = ∑ kk ∈ KF, ((G kk).image (fun p' => (kk, p'))).card := by
      dsimp only [GS]
      rw [Finset.card_biUnion]
      intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hza hzb
      simp only [Finset.mem_image] at hza hzb
      obtain ⟨pa, _, hpa⟩ := hza
      obtain ⟨pb, _, hpb⟩ := hzb
      exact hab (by simpa using congrArg Prod.fst (hpa.trans hpb.symm))
    have e2 : ∀ kk ∈ KF, ((G kk).image (fun p' => (kk, p'))).card = (G kk).card := by
      intro kk _
      rw [Finset.card_image_of_injective]
      intro a b h; simpa using h
    rw [e1, Finset.sum_congr rfl e2]
    push_cast
    rfl
  have hφinj : Set.InjOn φ (Qdom : Set _) := by
    intro t ht t' ht' heq
    obtain ⟨x'', ⟨xp', xp⟩⟩ := t
    obtain ⟨y'', ⟨yp', yp⟩⟩ := t'
    obtain ⟨hb, hbp⟩ := Finset.mem_sigma.mp ht
    obtain ⟨hb', hbp'⟩ := Finset.mem_sigma.mp ht'
    obtain ⟨hB, hA⟩ := Finset.mem_sigma.mp hbp
    obtain ⟨hB', hA'⟩ := Finset.mem_sigma.mp hbp'
    simp only [φ, Prod.mk.injEq] at heq
    obtain ⟨⟨hxx, hpp⟩, hpp'⟩ := heq
    have hA'eq : (xp.1, xp.2) ∈ Ainc yp'.1 := by
      have hthis : (xp.1, xp.2) = (yp.1, yp.2) := by rw [hxx, hpp']
      rw [hthis]; exact hA'
    have hx1 : xp'.1 ∈ F₁.fam := (Finset.mem_product.mp (Finset.mem_filter.mp hB).1).1
    have hy1 : yp'.1 ∈ F₁.fam := (Finset.mem_product.mp (Finset.mem_filter.mp hB').1).1
    have hx'eq : xp'.1 = yp'.1 :=
      incPairs_target_unique₂ (L := H) (L' := H / a₁) (R := 3 * H / a₁) F₁.isFam hx1 hy1 (by positivity)
        (by have hHp : 0 < H / a₁ := div_pos hH ha₁
            have hkey : 2 * (3 * H / a₁) = 6 * (H / a₁) := by ring
            rw [hkey]; linarith) hA hA'eq
    have hB'eq : (xp'.1, xp'.2) ∈ Binc y'' := by
      have hthis : (xp'.1, xp'.2) = (yp'.1, yp'.2) := by rw [hx'eq, hpp]
      rw [hthis]; exact hB'
    have hb2bound : (xp'.2 : ℝ) ≤ b₂ := by
      have h1 : xp'.2 ≤ ⌊b₂⌋₊ :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hB).1).2).1).2
      have h2 : (⌊b₂⌋₊ : ℝ) ≤ b₂ := Nat.floor_le (le_of_lt hb₂)
      have h3 : (xp'.2 : ℝ) ≤ (⌊b₂⌋₊ : ℝ) := by exact_mod_cast h1
      linarith
    have hx''eq : x'' = y'' :=
      incPairs_target_unique₂ (L := H / a₁) (L' := H / (a₁ * a₂)) (R := 3 * H / (a₁ * a₂))
        F₂.isFam hb hb' (by positivity) (by
          have hkey : 2 * (3 * H / (a₁ * a₂)) = 6 * (H / (a₁ * a₂)) := by ring
          rw [hkey]; linarith [hL₂pos]) hB hB'eq
    subst hx''eq
    have hpe : xp' = yp' := Prod.ext hx'eq hpp
    have hqe : xp = yp := Prod.ext hxx hpp'
    subst hpe
    subst hqe
    rfl
  have hGsum : c₀ * pi0 a₁ * (c₀ * pi0 a₂) * (c₂ * M) ≤ ∑ kk ∈ KF, ((G kk).card : ℝ) := by
    have hmaps : Set.MapsTo φ (Qdom : Set _) (GS : Set _) := by
      intro t ht
      obtain ⟨x'', ⟨xp', xp⟩⟩ := t
      obtain ⟨hb, hbp⟩ := Finset.mem_sigma.mp ht
      obtain ⟨hB, hA⟩ := Finset.mem_sigma.mp hbp
      have hp1 : xp'.1 ∈ F₁.fam := (Finset.mem_product.mp (Finset.mem_filter.mp hB).1).1
      have hpp : xp'.2 ∈ Pr₂ := (Finset.mem_product.mp (Finset.mem_filter.mp hB).1).2
      have hx0 : xp.1 ∈ F₀.fam := (Finset.mem_product.mp (Finset.mem_filter.mp hA).1).1
      have hkk : (xp.1, xp'.2) ∈ KF := by
        simp only [KF, Finset.mem_product]; exact ⟨hx0, hpp⟩
      have hmemG : xp.2 ∈ G (xp.1, xp'.2) := by
        rw [mem_G]
        exact ⟨xp'.1, hp1, hA, x'', hb, hB⟩
      refine Finset.mem_biUnion.mpr ⟨(xp.1, xp'.2), hkk, ?_⟩
      exact Finset.mem_image.mpr ⟨xp.2, hmemG, rfl⟩
    have h1 : (Qdom.card : ℝ) ≤ (GS.card : ℝ) := by
      exact_mod_cast Finset.card_le_card_of_injOn φ hmaps hφinj
    rw [hGS_card] at h1
    exact le_trans hQdom_ge h1
  -- ================= bounds on KF, DOM =================
  have hMval0 : M = X / H := rfl
  have hfam0 : (F₀.fam.card : ℝ) ≤ M / 40 := by
    have h := fam_card_le X H hX hH F₀.fam F₀.isFam
    have hMge : 200 ≤ M := by
      have h200 : 200 * b₁ ^ 2 ≤ M := by rw [hMval0]; exact hXH
      nlinarith [hb₁, h200]
    have h2 : 10 * X / (500 * H) + 1 = M / 50 + 1 := by rw [hMval0]; ring
    rw [h2] at h
    linarith
  have hfam2 : (F₂.fam.card : ℝ) ≤ M / 40 := by
    have h := fam_card_le (X / (a₁ * a₂)) (H / (a₁ * a₂)) (by positivity) (by positivity)
      F₂.fam F₂.isFam
    have hMge : 200 ≤ M := by
      have h200 : 200 * b₁ ^ 2 ≤ M := by rw [hMval0]; exact hXH
      nlinarith [hb₁, h200]
    have h2 : 10 * (X / (a₁ * a₂)) / (500 * (H / (a₁ * a₂))) + 1 = M / 50 + 1 := by
      rw [hMval0]; field_simp; ring
    rw [h2] at h
    linarith
  have hPr₁card : (Pr₁.card : ℝ) ≤ Cπ * pi0 a₁ :=
    hprime a₁ b₁ (le_trans hP₀π' hP₀a₁) ha₁b₁ (by linarith)
  have hPr₂card : (Pr₂.card : ℝ) ≤ Cπ * pi0 a₂ :=
    hprime a₂ b₂ (le_trans hP₀π' hP₀a₂) ha₂b₂ (by linarith)
  have hKFcard : (KF.card : ℝ) ≤ (M / 40) * (Cπ * pi0 a₂) := by
    simp only [KF, Finset.card_product]
    rw [Nat.cast_mul]
    exact mul_le_mul hfam0 hPr₂card (by positivity) (by positivity)
  -- ================= DOM cardinality via Cauchy-Schwarz =================
  have hDOMEq : (DOM.card : ℝ) =
      ((KF.sigma (fun kk => ((G kk).product (G kk)).filter (fun q : ℕ × ℕ => q.1 ≠ q.2))).card : ℝ) := by
    have h1 : DOM.card = ∑ kk ∈ KF, ((((G kk).product (G kk)).filter (fun q : ℕ × ℕ => q.1 ≠ q.2)).card) := by
      dsimp only [DOM]
      rw [Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro kk _
        rw [Finset.card_image_of_injective]
        intro a b h; simpa using h
      · intro a _ b _ hab
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro z hza hzb
        simp only [Finset.mem_image] at hza hzb
        obtain ⟨qa, _, hqa⟩ := hza
        obtain ⟨qb, _, hqb⟩ := hzb
        exact hab (by simpa using congrArg Prod.fst (hqa.trans hqb.symm))
    have h2 : ((KF.sigma (fun kk => ((G kk).product (G kk)).filter (fun q : ℕ × ℕ => q.1 ≠ q.2))).card)
        = ∑ kk ∈ KF, ((((G kk).product (G kk)).filter (fun q : ℕ × ℕ => q.1 ≠ q.2)).card) :=
      Finset.card_sigma KF (fun kk => ((G kk).product (G kk)).filter (fun q : ℕ × ℕ => q.1 ≠ q.2))
    rw [h1, h2]
  have hcard : (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
      - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ≤ (DOM.card : ℝ) := by
    have hs := sigma_filter_sq KF G ((M / 40) * (Cπ * pi0 a₂)) (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M)
      (by positivity) hKFcard (by positivity)
      (le_trans (by
        calc c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M = (c₀ ^ 3) * (pi0 a₁ * pi0 a₂) * M := by ring
          _ ≤ (c₀ * c₀ * c₂) * (pi0 a₁ * pi0 a₂) * M := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hMpos.le
              nlinarith [hc₀, hcc₂]
          _ = c₀ * pi0 a₁ * (c₀ * pi0 a₂) * (c₂ * M) := by ring) hGsum)
    rw [hDOMEq]
    exact hs
  -- ================= injectivity of (ed, prime) =================
  have hGsub : ∀ (kk : ℝ × ℕ) (p' : ℕ), p' ∈ G kk → p' ∈ Pr₁ := by
    intro kk p' hp'
    have h := hp'
    simp only [G, Finset.mem_filter] at h
    exact h.1
  have hle_primesIn : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ p ∈ primesIn a b, (p : ℝ) ≤ b := by
    intro a b _ hab p hp
    have h1 : p ≤ ⌊b⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by linarith)
    exact le_trans (by exact_mod_cast h1) h2
  have hge_primesIn : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ p ∈ primesIn a b, a ≤ (p : ℝ) := by
    intro a b _ _ p hp
    have h1 : (⌈a⌉₊ : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact le_trans (Nat.le_ceil a) h1
  have hkey : ∀ q ∈ DOM, ∀ q' ∈ DOM, ed q = ed q' → q.1.2 = q'.1.2 → q = q' := by
    intro q hq q' hq' heq hp
    obtain ⟨hKq, h1q, _, _⟩ := (mem_DOM q).mp hq
    obtain ⟨hKq', h1q', _, _⟩ := (mem_DOM q').mp hq'
    have hp1eq : q.2.1 = q'.2.1 := by
      have := congrArg Edge.p₁ heq; simpa [ed] using this
    have hp2eq : q.2.2 = q'.2.2 := by
      have := congrArg Edge.p₂ heq; simpa [ed] using this
    have hkv1 : q.1.2 ∈ Pr₂ := (Finset.mem_product.mp hKq).2
    have hkv1' : q'.1.2 ∈ Pr₂ := (Finset.mem_product.mp hKq').2
    have hb₂le : (q.1.2 : ℝ) ≤ b₂ := hle_primesIn a₂ b₂ ha₂ ha₂b₂ q.1.2 hkv1
    have hb₁le : (q.2.1 : ℝ) ≤ b₁ := hle_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.1 (hGsub q.1 q.2.1 h1q)
    have hZ1 : (wit q.1 q.2.1).2 = (wit q'.1 q'.2.1).2 := by
      have := congrArg Edge.x₁ heq; simpa [ed] using this
    have hX' : (wit q.1 q.2.1).1 = (wit q'.1 q'.2.1).1 := by
      have hb1 : ((wit q.1 q.2.1).1, q.1.2) ∈ Binc (wit q.1 q.2.1).2 := (wit_spec q.1 q.2.1 h1q).2.2.2
      have hb2 : ((wit q'.1 q'.2.1).1, q'.1.2) ∈ Binc (wit q.1 q.2.1).2 := by
        rw [hZ1]
        exact (wit_spec q'.1 q'.2.1 h1q').2.2.2
      have hR₂ : 2 * (b₂ : ℝ) * (3 * H / (a₁ * a₂)) < 500 * (H / a₁) := by
        have h6 : 6 * (b₂ : ℝ) / a₂ < 500 := by
          rw [div_lt_iff₀ ha₂]; nlinarith [hn₂]
        have hkey : 2 * (b₂ : ℝ) * (3 * H / (a₁ * a₂)) = (6 * (b₂ : ℝ) / a₂) * (H / a₁) := by
          field_simp; ring
        rw [hkey]
        exact mul_lt_mul_of_pos_right h6 (div_pos hH ha₁)
      exact incPairs_fst_unique₂ (b := b₂) (R := 3 * H / (a₁ * a₂)) (L := H / a₁)
        F₁.isFam (by positivity) hR₂ hp hb1 hb2 hb₂le
    have hXeq : q.1.1 = q'.1.1 := by
      have ha1 : (q.1.1, q.2.1) ∈ Ainc (wit q.1 q.2.1).1 := (wit_spec q.1 q.2.1 h1q).2.1
      have ha2 : (q'.1.1, q'.2.1) ∈ Ainc (wit q.1 q.2.1).1 := by
        rw [hX']
        exact (wit_spec q'.1 q'.2.1 h1q').2.1
      have hR₁ : 2 * (b₁ : ℝ) * (3 * H / a₁) < 500 * H := by
        have h6 : (6 * (b₁ : ℝ)) < 500 * a₁ := by nlinarith
        have hkey : 2 * (b₁ : ℝ) * (3 * H / a₁) = (6 * (b₁ : ℝ) / a₁) * H := by
          field_simp; ring
        rw [hkey]
        exact mul_lt_mul_of_pos_right (by rw [div_lt_iff₀ ha₁]; linarith) hH
      exact incPairs_fst_unique₂ (b := b₁) (R := 3 * H / a₁) (L := H)
        F₀.isFam (by positivity) hR₁ hp1eq ha1 ha2 hb₁le
    have hq1 : q.1 = q'.1 := Prod.ext hXeq hp
    have hq2 : q.2 = q'.2 := Prod.ext hp1eq hp2eq
    exact Prod.ext hq1 hq2
  have hFcard : ∀ e : Edge, ((DOM.filter (fun q => ed q = e)).card : ℝ) ≤ (Pr₂.card : ℝ) := by
    intro e
    have hmaps : Set.MapsTo (fun q : (ℝ × ℕ) × (ℕ × ℕ) => q.1.2)
        ((DOM.filter (fun q => ed q = e)) : Set _) (Pr₂ : Set _) := by
      intro q hq
      exact (Finset.mem_product.mp ((mem_DOM q).mp (Finset.mem_filter.mp hq).1).1).2
    have hinj : Set.InjOn (fun q : (ℝ × ℕ) × (ℕ × ℕ) => q.1.2)
        ((DOM.filter (fun q => ed q = e)) : Set _) := by
      intro a ha b hb hab
      exact hkey a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (by rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]) hab
    exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
  -- geometric estimate
  have hgeo : ∀ (kk : ℝ × ℕ) (p' : ℕ), kk ∈ KF → p' ∈ G kk →
      |(wit kk p').2 - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))| ≤ 6 * L₂ := by
    intro kk p' hkk hp'
    have hspec := wit_spec kk p' hp'
    have hk2 : kk.2 ∈ Pr₂ := (Finset.mem_product.mp hkk).2
    have hmem1 : (kk.1, p') ∈ Ainc (wit kk p').1 := hspec.2.1
    have hmem2 : ((wit kk p').1, kk.2) ∈ Binc (wit kk p').2 := hspec.2.2.2
    have hd1 : |kk.1 / (p' : ℝ) - (wit kk p').1| ≤ 3 * L₁ := by
      have h := (Finset.mem_filter.mp hmem1).2.1
      rw [hL₁v]; convert h using 1; ring
    have hd2 : |(wit kk p').1 / (kk.2 : ℝ) - (wit kk p').2| ≤ 3 * L₂ := by
      have h := (Finset.mem_filter.mp hmem2).2.1
      rw [hL₂v]; convert h using 1; ring
    have hp2pos : (0 : ℝ) < (kk.2 : ℝ) := by
      have h := hge_primesIn a₂ b₂ ha₂ ha₂b₂ kk.2 hk2; linarith
    have hp2a : a₂ ≤ (kk.2 : ℝ) := hge_primesIn a₂ b₂ ha₂ ha₂b₂ kk.2 hk2
    have hp'pos : (0 : ℝ) < (p' : ℝ) := by
      have h := hge_primesIn a₁ b₁ ha₁ ha₁b₁ p' (hGsub kk p' hp'); linarith
    have hstep2 : |(wit kk p').1 / (kk.2 : ℝ) - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))| ≤ 3 * L₂ := by
      have hEq : (wit kk p').1 / (kk.2 : ℝ) - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))
          = (1 / (kk.2 : ℝ)) * ((wit kk p').1 - kk.1 / (p' : ℝ)) := by
        field_simp
      rw [hEq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (kk.2 : ℝ))]
      calc (1 / (kk.2 : ℝ)) * |(wit kk p').1 - kk.1 / (p' : ℝ)|
          ≤ (1 / (kk.2 : ℝ)) * (3 * L₁) :=
            mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hd1) (by positivity)
        _ ≤ 3 * L₂ := by
            rw [hL₁v, hL₂v]
            have h1 : (0 : ℝ) ≤ 3 * H := by positivity
            have h2 : 0 < a₁ * a₂ := by positivity
            have h3 : a₁ * a₂ ≤ a₁ * (kk.2 : ℝ) := by nlinarith [ha₁, hp2a]
            have h4 : (1 / (kk.2 : ℝ)) * (3 * (H / a₁)) = 3 * H / (a₁ * (kk.2 : ℝ)) := by
              field_simp
            rw [h4, show 3 * (H / (a₁ * a₂)) = 3 * H / (a₁ * a₂) by ring]
            exact div_le_div_of_nonneg_left h1 h2 h3
    calc |(wit kk p').2 - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))|
        ≤ |(wit kk p').2 - (wit kk p').1 / (kk.2 : ℝ)|
          + |(wit kk p').1 / (kk.2 : ℝ) - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))| := by
          rw [show (wit kk p').2 - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))
              = ((wit kk p').2 - (wit kk p').1 / (kk.2 : ℝ))
                + ((wit kk p').1 / (kk.2 : ℝ) - kk.1 / ((p' : ℝ) * (kk.2 : ℝ))) by ring]
          exact abs_add_le _ _
      _ ≤ 3 * L₂ + 3 * L₂ := by
          have : |(wit kk p').2 - (wit kk p').1 / (kk.2 : ℝ)| ≤ 3 * L₂ := by
            rw [abs_sub_comm]; exact hd2
          linarith
      _ ≤ 6 * L₂ := by linarith
  have hgeomE : ∀ q ∈ DOM, |(ed q).x₁ - ((ed q).p₂ / (ed q).p₁) * (ed q).x₂| ≤ 100 * L₂ := by
    intro q hq
    obtain ⟨hKq, h1q, h2q, hne⟩ := (mem_DOM q).mp hq
    have hg1 := hgeo q.1 q.2.1 hKq h1q
    have hg2 := hgeo q.1 q.2.2 hKq h2q
    have hp1pos : (0 : ℝ) < (q.2.1 : ℝ) := by
      have h := hge_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.1 (hGsub q.1 q.2.1 h1q); linarith
    have hratio : (q.2.2 : ℝ) / (q.2.1 : ℝ) ≤ 2 := by
      have h2 : (q.2.2 : ℝ) ≤ b₁ := hle_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.2 (hGsub q.1 q.2.2 h2q)
      have h1 : a₁ ≤ (q.2.1 : ℝ) := hge_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.1 (hGsub q.1 q.2.1 h1q)
      have hb1' : b₁ ≤ 2 * a₁ := by linarith
      rw [div_le_iff₀ hp1pos]
      nlinarith [h1, h2, hb1']
    have hpos22 : (0 : ℝ) < (q.2.2 : ℝ) := by
      have := hge_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.2 (hGsub q.1 q.2.2 h2q); linarith
    have hne22 : (q.2.2 : ℝ) ≠ 0 := ne_of_gt hpos22
    have hratio0 : 0 ≤ (q.2.2 : ℝ) / (q.2.1 : ℝ) := by positivity
    have hstep : |q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ)) - ((q.2.2 : ℝ) / (q.2.1 : ℝ)) * (ed q).x₂|
        ≤ ((q.2.2 : ℝ) / (q.2.1 : ℝ)) * (6 * L₂) := by
      have hEq : q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ)) - ((q.2.2 : ℝ) / (q.2.1 : ℝ)) * (ed q).x₂
          = ((q.2.2 : ℝ) / (q.2.1 : ℝ))
            * (q.1.1 / ((q.2.2 : ℝ) * (q.1.2 : ℝ)) - (ed q).x₂) := by
        field_simp; try ring
      have hg2' : |(ed q).x₂ - q.1.1 / ((q.2.2 : ℝ) * (q.1.2 : ℝ))| ≤ 6 * L₂ := by
        simpa [ed] using hg2
      rw [hEq, abs_mul, abs_of_nonneg hratio0]
      exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hg2') hratio0
    calc |(ed q).x₁ - ((ed q).p₂ / (ed q).p₁) * (ed q).x₂|
        ≤ |(ed q).x₁ - q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ))|
          + |q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ)) - ((ed q).p₂ / (ed q).p₁) * (ed q).x₂| := by
          rw [show (ed q).x₁ - ((ed q).p₂ / (ed q).p₁) * (ed q).x₂
              = ((ed q).x₁ - q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ)))
                + (q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ)) - ((ed q).p₂ / (ed q).p₁) * (ed q).x₂) by ring]
          exact abs_add_le _ _
      _ ≤ 6 * L₂ + 2 * (6 * L₂) := by
          have h1 : |(ed q).x₁ - q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ))| ≤ 6 * L₂ := by
            simpa [ed] using hg1
          have h2 : |q.1.1 / ((q.2.1 : ℝ) * (q.1.2 : ℝ)) - ((ed q).p₂ / (ed q).p₁) * (ed q).x₂|
              ≤ 2 * (6 * L₂) := by
            have heq1 : (ed q).p₁ = q.2.1 := rfl
            have heq2 : (ed q).p₂ = q.2.2 := rfl
            rw [heq1, heq2]
            exact le_trans hstep (by nlinarith [hratio])
          linarith
      _ ≤ 100 * L₂ := by linarith [hL₂pos]
  have hEcard : ((DOM.image ed).card : ℝ) ≤ (F₂.fam.card : ℝ) * (Pr₁.card : ℝ) * (Pr₁.card : ℝ) := by
    have hmaps : Set.MapsTo (fun e : Edge => ((e.x₂, e.p₁), e.p₂))
        ((DOM.image ed) : Set _) (((F₂.fam ×ˢ Pr₁) ×ˢ Pr₁ : Finset ((ℝ × ℕ) × ℕ)) : Set _) := by
      intro e he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hKq, h1q, h2q, _⟩ := (mem_DOM q).mp hq
      have hspec2 := wit_spec q.1 q.2.2 h2q
      have hx2 : (ed q).x₂ ∈ F₂.fam := by simpa [ed] using hspec2.2.2.1
      have hp1 : (ed q).p₁ ∈ Pr₁ := by simpa [ed] using hGsub q.1 q.2.1 h1q
      have hp2 : (ed q).p₂ ∈ Pr₁ := by simpa [ed] using hGsub q.1 q.2.2 h2q
      simp only [Finset.mem_coe, Finset.mem_product]
      exact ⟨⟨hx2, hp1⟩, hp2⟩
    have hinj : Set.InjOn (fun e : Edge => ((e.x₂, e.p₁), e.p₂)) ((DOM.image ed) : Set _) := by
      intro e he e' he' heq
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨q', hq', hq'eq⟩ := Finset.mem_image.mp he'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨hx2eq, hp1eq⟩, hp2eq⟩ := heq
      rw [← hq'eq] at hx2eq hp1eq hp2eq
      have hgeo2 := hgeomE q hq
      have hgeo2' := hgeomE q' hq'
      have hx1eq : (ed q).x₁ = (ed q').x₁ := by
        have hZ : ((ed q).p₂ / (ed q).p₁) * (ed q).x₂ = ((ed q').p₂ / (ed q').p₁) * (ed q').x₂ := by
          rw [hp2eq, hp1eq, hx2eq]
        refine F₂.isFam.eq_of_abs_sub_lt
          (by simpa [ed] using (wit_spec q.1 q.2.1 (((mem_DOM q).mp hq).2.1)).2.2.1)
          (by simpa [ed] using (wit_spec q'.1 q'.2.1 (((mem_DOM q').mp hq').2.1)).2.2.1) ?_
        rw [hZ] at hgeo2
        have h2 := abs_sub_le_iff.mp (by simpa [hL₂v] using hgeo2)
        have h3 := abs_sub_le_iff.mp (by simpa [hL₂v] using hgeo2')
        have h4 : |(ed q).x₁ - (ed q').x₁| ≤ 100 * L₂ + 100 * L₂ := by
          calc |(ed q).x₁ - (ed q').x₁|
              ≤ |(ed q).x₁ - ((ed q').p₂ / (ed q').p₁) * (ed q').x₂|
                + |((ed q').p₂ / (ed q').p₁) * (ed q').x₂ - (ed q').x₁| := by
                rw [show (ed q).x₁ - (ed q').x₁
                    = ((ed q).x₁ - ((ed q').p₂ / (ed q').p₁) * (ed q').x₂)
                      + (((ed q').p₂ / (ed q').p₁) * (ed q').x₂ - (ed q').x₁) by ring]
                exact abs_add_le _ _
            _ ≤ 100 * L₂ + 100 * L₂ := by
                have h5 : |((ed q').p₂ / (ed q').p₁) * (ed q').x₂ - (ed q').x₁| ≤ 100 * L₂ := by
                  rw [abs_sub_comm]; exact hgeo2'
                linarith [hgeo2, h5]
        have hfin : 200 * L₂ < 500 * L₂ := by linarith [hL₂pos]
        linarith [h4, hfin]
      rw [← hq'eq]
      simp only [ed, Edge.mk.injEq]
      exact ⟨hx1eq, hx2eq, hp1eq, hp2eq⟩
    have hcard' := Finset.card_le_card_of_injOn (fun e : Edge => ((e.x₂, e.p₁), e.p₂)) hmaps hinj
    have hcard'' : (((F₂.fam ×ˢ Pr₁) ×ˢ Pr₁ : Finset ((ℝ × ℕ) × ℕ))).card
        = F₂.fam.card * Pr₁.card * Pr₁.card := by
      rw [Finset.card_product, Finset.card_product]
    rw [hcard''] at hcard'
    exact_mod_cast hcard'
  -- ================= the CRT correction and the modified phases =================
  let Ip : ℝ → Finset ℕ := fun y => Pr₂.filter (fun p => ∃ x' ∈ F₁.fam, (x', p) ∈ Binc y)
  have mem_Ip : ∀ y p, p ∈ Ip y ↔ p ∈ Pr₂ ∧ ∃ x' ∈ F₁.fam, (x', p) ∈ Binc y := by
    intro y p; simp only [Ip, Finset.mem_filter]
  let xsrc : ℝ → ℕ → ℝ := fun y p =>
    if _ : ∃ x' ∈ F₁.fam, (x', p) ∈ Binc y then Classical.choose (by assumption) else 0
  have xsrc_spec : ∀ y p, p ∈ Ip y → xsrc y p ∈ F₁.fam ∧ (xsrc y p, p) ∈ Binc y := by
    intro y p hp
    have h : ∃ x' ∈ F₁.fam, (x', p) ∈ Binc y := ((mem_Ip y p).mp hp).2
    dsimp only [xsrc]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hrel_exists : ∀ y p, p ∈ Ip y → ∃ ε γ : ℝ[X],
      ε ∈ degreeLE ℝ (k : WithBot ℕ) ∧ γ ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      dil (p : ℝ) (F₁.pol (xsrc y p)) = ε + F₂.pol y + γ ∧
      (∀ t ∈ Set.Icc ((xsrc y p) / (p : ℝ))
        ((xsrc y p) / (p : ℝ) + (H / a₁) / (p : ℝ)), |ε.eval t| ≤ Cᵢ) ∧ IntegralOn 1 γ := by
    intro y p hp
    have h2mem := (xsrc_spec y p hp).2
    have hcond := (Finset.mem_filter.mp h2mem).2
    obtain ⟨h1, h2, h3, ε, γ, hε, hγ, heq, hbdd, hint⟩ := hcond.2
    exact ⟨ε, γ, hε, hγ, heq, hbdd, hint⟩
  let gerrE : ℝ → ℕ → ℝ[X] := fun y p => if h : (∃ ε γ : ℝ[X],
      ε ∈ degreeLE ℝ (k : WithBot ℕ) ∧ γ ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      dil (p : ℝ) (F₁.pol (xsrc y p)) = ε + F₂.pol y + γ ∧
      (∀ t ∈ Set.Icc ((xsrc y p) / (p : ℝ))
        ((xsrc y p) / (p : ℝ) + (H / a₁) / (p : ℝ)), |ε.eval t| ≤ Cᵢ) ∧ IntegralOn 1 γ)
    then Classical.choose h else 0
  let gerrG : ℝ → ℕ → ℝ[X] := fun y p => if h : (∃ ε γ : ℝ[X],
      ε ∈ degreeLE ℝ (k : WithBot ℕ) ∧ γ ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      dil (p : ℝ) (F₁.pol (xsrc y p)) = ε + F₂.pol y + γ ∧
      (∀ t ∈ Set.Icc ((xsrc y p) / (p : ℝ))
        ((xsrc y p) / (p : ℝ) + (H / a₁) / (p : ℝ)), |ε.eval t| ≤ Cᵢ) ∧ IntegralOn 1 γ)
    then Classical.choose (Classical.choose_spec h) else 0
  have gerr_spec : ∀ y p (hp : p ∈ Ip y), gerrE y p ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      gerrG y p ∈ degreeLE ℝ (k : WithBot ℕ) ∧ IntegralOn 1 (gerrG y p) ∧
      dil (p : ℝ) (F₁.pol (xsrc y p)) = gerrE y p + F₂.pol y + gerrG y p ∧
      (∀ t ∈ Set.Icc ((xsrc y p) / (p : ℝ))
        ((xsrc y p) / (p : ℝ) + (H / a₁) / (p : ℝ)), |(gerrE y p).eval t| ≤ Cᵢ) := by
    intro y p hp
    have hh := hrel_exists y p hp
    have h1 : gerrE y p = Classical.choose hh := by dsimp only [gerrE]; rw [dif_pos hh]
    have h2 : gerrG y p = Classical.choose (Classical.choose_spec hh) := by
      dsimp only [gerrG]; rw [dif_pos hh]
    rw [h1, h2]
    obtain ⟨hp1, hp2, hpe, hpb, hpi⟩ := Classical.choose_spec (Classical.choose_spec hh)
    exact ⟨hp1, hp2, hpi, hpe, hpb⟩
  have hcrt : ∀ y ∈ F₂.fam, ∃ gt : ℝ[X], gt ∈ degreeLE ℝ (k : WithBot ℕ) ∧ IntegralOn 1 gt ∧
      (∀ p, p ∈ Ip y → IntegralOn (1 / (p : ℝ)) (gerrG y p - gt)) := by
    intro y _
    refine crt_intValued k (Ip y) (fun p hp => ?_) (fun p => gerrG y p) (fun p hp => ?_) (fun p hp => ?_)
    · exact (Finset.mem_filter.mp ((mem_Ip y p).mp hp).1).2
    · exact (gerr_spec y p hp).2.1
    · exact (gerr_spec y p hp).2.2.1
  let cpol : ℝ → ℝ[X] := fun y => if h : (∃ gt : ℝ[X], gt ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      IntegralOn 1 gt ∧ (∀ p, p ∈ Ip y → IntegralOn (1 / (p : ℝ)) (gerrG y p - gt)))
    then F₂.pol y + Classical.choose h else F₂.pol y
  have cpol_spec : ∀ y ∈ F₂.fam, ∃ gt : ℝ[X], gt ∈ degreeLE ℝ (k : WithBot ℕ) ∧ IntegralOn 1 gt ∧
      cpol y = F₂.pol y + gt ∧ (∀ p, p ∈ Ip y → IntegralOn (1 / (p : ℝ)) (gerrG y p - gt)) := by
    intro y hy
    have hh := hcrt y hy
    refine ⟨Classical.choose hh, (Classical.choose_spec hh).1, (Classical.choose_spec hh).2.1, ?_,
      (Classical.choose_spec hh).2.2⟩
    dsimp only [cpol]
    rw [dif_pos hh]
  have cpol_deg : ∀ y ∈ F₂.fam, cpol y ∈ degreeLE ℝ (k : WithBot ℕ) := by
    intro y hy
    obtain ⟨gt, h1, h2, h3, h4⟩ := cpol_spec y hy
    rw [h3]
    exact Submodule.add_mem _ (F₂.deg y hy) h1
  have cpol_corr : ∀ y ∈ F₂.fam, corr f (cpol y) y L₂ = corr f (F₂.pol y) y L₂ := by
    intro y hy
    obtain ⟨gt, h1, h2, h3, h4⟩ := cpol_spec y hy
    rw [h3]
    exact corr_add_integral f h2

  -- ================= the CRT-upgraded relation for the second family =================
  have upgraded : ∀ (y : ℝ) (p : ℕ) (X' : ℝ), y ∈ F₂.fam → p ∈ Ip y → (X', p) ∈ Binc y →
      PolyRel k Cᵢ (1 / (p : ℝ)) (X' / (p : ℝ)) (L₁ / (p : ℝ)) (dil (p : ℝ) (F₁.pol X'))
        y L₂ (cpol y) := by
    intro y p X' hy hpI hpB
    obtain ⟨gt, hgtdeg, hgtint, hcpol, hrel⟩ := cpol_spec y hy
    have hsrc : xsrc y p = X' := by
      have h1 := (xsrc_spec y p hpI).2
      exact incPairs_fst_unique₂ (b := b₂) (R := 3 * H / (a₁ * a₂)) (L := H / a₁) F₁.isFam
        (by positivity) (by
          have h6 : 6 * (b₂ : ℝ) / a₂ < 500 := by rw [div_lt_iff₀ ha₂]; nlinarith [hn₂]
          have hkey : 2 * (b₂ : ℝ) * (3 * H / (a₁ * a₂)) = (6 * (b₂ : ℝ) / a₂) * (H / a₁) := by
            field_simp; ring
          rw [hkey]
          exact mul_lt_mul_of_pos_right h6 (div_pos hH ha₁)) rfl h1 hpB
        (hle_primesIn a₂ b₂ ha₂ ha₂b₂ p (Finset.mem_product.mp (Finset.mem_filter.mp hpB).1).2)
    have hspec := gerr_spec y p hpI
    obtain ⟨hc1, hc2, hc3, _⟩ := (Finset.mem_filter.mp hpB).2.2
    refine ⟨hc1, hc2, hc3, gerrE y p, gerrG y p - gt, hspec.1,
      Submodule.sub_mem _ hspec.2.1 hgtdeg, ?_, ?_, hrel p hpI⟩
    · calc dil (p : ℝ) (F₁.pol X')
          = dil (p : ℝ) (F₁.pol (xsrc y p)) := by rw [hsrc]
        _ = gerrE y p + F₂.pol y + gerrG y p := hspec.2.2.2.1
        _ = gerrE y p + cpol y + (gerrG y p - gt) := by rw [hcpol]; ring
    · intro t ht
      have ht' : t ∈ Set.Icc (xsrc y p / (p : ℝ))
          (xsrc y p / (p : ℝ) + (H / a₁) / (p : ℝ)) := by
        rw [← hsrc] at ht
        rw [← hL₁v]
        exact ht
      exact hspec.2.2.2.2 t ht'
  -- ================= the edge relation =================
  have hedrel : ∀ q ∈ DOM, EdgeRel k C (1 / (q.1.2 : ℝ)) L₂ cpol (ed q) := by
    intro q hq
    obtain ⟨hKq, h1q, h2q, hne⟩ := (mem_DOM q).mp hq
    have hq1 := wit_spec q.1 q.2.1 h1q
    have hq2 := wit_spec q.1 q.2.2 h2q
    have hp1pos : (0 : ℝ) < (q.2.1 : ℝ) := by
      have := hge_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.1 (hGsub q.1 q.2.1 h1q); linarith
    have hp2pos : (0 : ℝ) < (q.2.2 : ℝ) := by
      have := hge_primesIn a₁ b₁ ha₁ ha₁b₁ q.2.2 (hGsub q.1 q.2.2 h2q); linarith
    have hpk : (0 : ℝ) < (q.1.2 : ℝ) := by
      have := hge_primesIn a₂ b₂ ha₂ ha₂b₂ q.1.2 ((Finset.mem_product.mp hKq).2); linarith
    have hpI1 : q.1.2 ∈ Ip (wit q.1 q.2.1).2 := by
      rw [mem_Ip]
      exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hq1.2.2.2).1).2,
        ⟨(wit q.1 q.2.1).1, hq1.1, hq1.2.2.2⟩⟩
    have hpI2 : q.1.2 ∈ Ip (wit q.1 q.2.2).2 := by
      rw [mem_Ip]
      exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hq2.2.2.2).1).2,
        ⟨(wit q.1 q.2.2).1, hq2.1, hq2.2.2.2⟩⟩
    have h1rel : PolyRel k Cᵢ 1 (q.1.1 / (q.2.1 : ℝ)) (H / (q.2.1 : ℝ))
        (dil (q.2.1 : ℝ) (F₀.pol q.1.1)) (wit q.1 q.2.1).1 L₁ (F₁.pol (wit q.1 q.2.1).1) :=
      (Finset.mem_filter.mp hq1.2.1).2.2
    have h2rel : PolyRel k Cᵢ 1 (q.1.1 / (q.2.2 : ℝ)) (H / (q.2.2 : ℝ))
        (dil (q.2.2 : ℝ) (F₀.pol q.1.1)) (wit q.1 q.2.2).1 L₁ (F₁.pol (wit q.1 q.2.2).1) :=
      (Finset.mem_filter.mp hq2.2.1).2.2
    have h3rel := upgraded (wit q.1 q.2.1).2 q.1.2 (wit q.1 q.2.1).1 hq1.2.2.1 hpI1 hq1.2.2.2
    have h4rel := upgraded (wit q.1 q.2.2).2 q.1.2 (wit q.1 q.2.2).1 hq2.2.2.1 hpI2 hq2.2.2.2
    have hchain := polyrel_chain (Cᵢ := Cᵢ) (H₁ := H) (L₁ := L₁) (L₂ := L₂) (x := q.1.1)
      (X'₁ := (wit q.1 q.2.1).1) (X'₂ := (wit q.1 q.2.2).1) (Z₁ := (wit q.1 q.2.1).2)
      (Z₂ := (wit q.1 q.2.2).2) (p'₁ := q.2.1) (p'₂ := q.2.2) (p := q.1.2)
      (P := F₀.pol q.1.1) (P₁ := F₁.pol (wit q.1 q.2.1).1) (P₂ := F₁.pol (wit q.1 q.2.2).1)
      (g := cpol) (C := C) hCᵢ hp1pos hp2pos hpk hH hL₁pos hL₂pos h1rel h2rel h3rel h4rel hC
    simpa only [ed, EdgeRel] using hchain
  -- ================= the non-degeneracy of an edge =================
  have hne_edge : ∀ q ∈ DOM, (ed q).x₁ ≠ (ed q).x₂ := by
    intro q hq hEq
    obtain ⟨hKq, h1q, h2q, hne⟩ := (mem_DOM q).mp hq
    have hq1 := wit_spec q.1 q.2.1 h1q
    have hq2 := wit_spec q.1 q.2.2 h2q
    have hZ : (wit q.1 q.2.1).2 = (wit q.1 q.2.2).2 := by simpa [ed] using hEq
    have hB2 : ((wit q.1 q.2.2).1, q.1.2) ∈ Binc (wit q.1 q.2.2).2 := hq2.2.2.2
    rw [← hZ] at hB2
    have hx'eq : (wit q.1 q.2.1).1 = (wit q.1 q.2.2).1 := by
      exact incPairs_fst_unique₂ (b := b₂) (R := 3 * H / (a₁ * a₂)) (L := H / a₁) F₁.isFam
        (by positivity) (by
          have h6 : 6 * (b₂ : ℝ) / a₂ < 500 := by rw [div_lt_iff₀ ha₂]; nlinarith [hn₂]
          have hkey : 2 * (b₂ : ℝ) * (3 * H / (a₁ * a₂)) = (6 * (b₂ : ℝ) / a₂) * (H / a₁) := by
            field_simp; ring
          rw [hkey]
          exact mul_lt_mul_of_pos_right h6 (div_pos hH ha₁)) rfl hq1.2.2.2 hB2
        (hle_primesIn a₂ b₂ ha₂ ha₂b₂ q.1.2 ((Finset.mem_product.mp hKq).2))
    have h2mem : (q.1.1, q.2.2) ∈
        incPairs k Cᵢ F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol
          (F₁.pol (wit q.1 q.2.1).1) (wit q.1 q.2.1).1 := by
      have h := hq2.2.1
      rw [← hx'eq] at h
      exact h
    exact incPairs_two_primes_forbidden F₀.isFam ha₁ hb₁ hH hn₁ hXH hX
      (by linarith [hP₀4, hP₀a₁]) hne hq1.2.1 h2mem
  -- ================= the geometry of an edge =================
  have hedgeom : ∀ q ∈ DOM, EdgeGeom F₂.fam (a₁ * a₂ / b₂) L₂ (ed q) := by
    intro q hq
    obtain ⟨hKq, h1q, h2q, hne⟩ := (mem_DOM q).mp hq
    have hq1 := wit_spec q.1 q.2.1 h1q
    have hq2 := wit_spec q.1 q.2.2 h2q
    have hp1mem : (ed q).p₁ ∈ Pr₁ := by simpa [ed] using hGsub q.1 q.2.1 h1q
    have hp2mem : (ed q).p₂ ∈ Pr₁ := by simpa [ed] using hGsub q.1 q.2.2 h2q
    have hp1prime : (ed q).p₁.Prime := (Finset.mem_filter.mp hp1mem).2
    have hp2prime : (ed q).p₂.Prime := (Finset.mem_filter.mp hp2mem).2
    have hp1ge : a₁ ≤ ((ed q).p₁ : ℝ) := hge_primesIn a₁ b₁ ha₁ ha₁b₁ _ hp1mem
    have hp2lb : ((ed q).p₂ : ℝ) ≤ b₁ := hle_primesIn a₁ b₁ ha₁ ha₁b₁ _ hp2mem
    have hp2ge : a₁ ≤ ((ed q).p₂ : ℝ) := hge_primesIn a₁ b₁ ha₁ ha₁b₁ _ hp2mem
    have hp1lb : ((ed q).p₁ : ℝ) ≤ b₁ := hle_primesIn a₁ b₁ ha₁ ha₁b₁ _ hp1mem
    have hP₁pos : 0 < a₁ * a₂ / b₂ := by
      refine div_pos (mul_pos ha₁ ha₂) hb₂
    have hP₁a : a₁ * a₂ / b₂ ≤ a₁ := by rw [div_le_iff₀ hb₂]; nlinarith [ha₂b₂, ha₁]
    have hP₁le : a₁ * a₂ / b₂ ≤ ((ed q).p₁ : ℝ) := le_trans hP₁a hp1ge
    have hP₁le2 : a₁ * a₂ / b₂ ≤ ((ed q).p₂ : ℝ) := le_trans hP₁a hp2ge
    have hP₁ub1 : ((ed q).p₁ : ℝ) ≤ 2 * (a₁ * a₂ / b₂) := by
      rw [show 2 * (a₁ * a₂ / b₂) = 2 * (a₁ * a₂) / b₂ by ring, le_div_iff₀ hb₂]
      nlinarith [hb₁b₂, hp1lb, hb₂]
    have hP₁ub2 : ((ed q).p₂ : ℝ) ≤ 2 * (a₁ * a₂ / b₂) := by
      rw [show 2 * (a₁ * a₂ / b₂) = 2 * (a₁ * a₂) / b₂ by ring, le_div_iff₀ hb₂]
      nlinarith [hb₁b₂, hp2lb, hb₂]
    refine ⟨by simpa [ed] using hq1.2.2.1, by simpa [ed] using hq2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact hne_edge q hq (by simpa [ed] using h)
    · simpa [ed] using hne
    · exact ⟨hp1prime, hP₁le, hP₁ub1⟩
    · exact ⟨hp2prime, hP₁le2, hP₁ub2⟩
    · simpa [ed] using hgeomE q hq

  -- ================= the lower bound for `π₀(a₁)` =================
  have hπ₁big : Cπ / (20 * c₀ ^ 3) + 1 ≤ pi0 a₁ :=
    qd_pi0_ge_of_big hc₀ hCπ ha₁1 hP₀a₁ hP₀big
  -- ================= the counting bound =================
  have hQK : 20 * c₀ ^ 6 * pi0 a₁ ^ 2 * pi0 a₂ * M / Cπ
      ≤ (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
        - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) :=
    qd_qk_bound hc₀ hCπ hπ₁big hπ₂pos hMpos
  have hDOMpos : 0 < (DOM.card : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hQK) hcard
  -- ================= the compactness bound =================
  have hEcard' : ((DOM.image ed).card : ℝ) ≤ (M / 40) * (Cπ * pi0 a₁) ^ 2 := by
    refine le_trans hEcard ?_
    calc (F₂.fam.card : ℝ) * (Pr₁.card : ℝ) * (Pr₁.card : ℝ)
        ≤ (M / 40) * (Cπ * pi0 a₁) * (Cπ * pi0 a₁) := by
          have h1 : (Pr₁.card : ℝ) * (Pr₁.card : ℝ)
              ≤ (Cπ * pi0 a₁) * (Cπ * pi0 a₁) :=
            mul_le_mul hPr₁card hPr₁card (by positivity) (by positivity)
          nlinarith [h1, hfam2, hMpos]
      _ = (M / 40) * (Cπ * pi0 a₁) ^ 2 := by ring
  obtain ⟨Aa, hAcard, hASAe⟩ := edge_count_core KF G DOM ed hkey
    (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ((M / 40) * (Cπ * pi0 a₂))
    ((M / 40) * (Cπ * pi0 a₁) ^ 2) (Cπ * pi0 a₂)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hKFcard hcard hEcard' (fun e => le_trans (hFcard e) hPr₂card)
  have hEmaxpos : (0 : ℝ) < (M / 40) * (Cπ * pi0 a₁) ^ 2 := by positivity
  have hEmax2pos : (0 : ℝ) < 2 * ((M / 40) * (Cπ * pi0 a₁) ^ 2) := by positivity
  have hFmaxpos : (0 : ℝ) < 2 * (Cπ * pi0 a₂) := by positivity
  have hDOMfacpos : (0 : ℝ) < (DOM.card : ℝ) / (2 * ((M / 40) * (Cπ * pi0 a₁) ^ 2)) := by
    positivity
  -- ================= the two lower bounds for `|Aa|` and the moduli =================
  have hAcardM : c * pi0 (a₁ * a₂ / b₂) ^ 2 * M ≤ (Aa.card : ℝ) := by
    have h4 : ((c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
          - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M)) / (2 * (Cπ * pi0 a₂)) ≤ (Aa.card : ℝ) := by
      rw [div_le_iff₀ hFmaxpos] at hAcard ⊢
      linarith [hcard]
    have h1 : c * (4 * pi0 a₁ ^ 2 * M) ≤
        ((c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
          - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M)) / (2 * (Cπ * pi0 a₂)) := by
      rw [le_div_iff₀ hFmaxpos]
      exact qd_edge_lower hc hc₀ hCπ hπ₁big hπ₂pos hMpos hc1
    have hP1lb : a₁ / 2 ≤ a₁ * a₂ / b₂ := by
      rw [le_div_iff₀ hb₂]; nlinarith [ha₁, ha₂b₂, hb₂]
    have hP1ub : a₁ * a₂ / b₂ ≤ a₁ := by
      rw [div_le_iff₀ hb₂]; nlinarith [ha₁, ha₂b₂]
    have h5 : pi0 (a₁ * a₂ / b₂) ^ 2 ≤ 4 * pi0 a₁ ^ 2 :=
      qd_pi0_half (by linarith [hP₀4, hP₀a₁]) hP1lb hP1ub
    calc c * pi0 (a₁ * a₂ / b₂) ^ 2 * M
        ≤ c * (4 * pi0 a₁ ^ 2) * M := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hc.le) hMpos.le
      _ = c * (4 * pi0 a₁ ^ 2 * M) := by ring
      _ ≤ (Aa.card : ℝ) := le_trans h1 h4
  have hSb : c * (2 * pi0 a₂) ≤
      ((c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
        - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M)) / (2 * ((M / 40) * (Cπ * pi0 a₁) ^ 2)) := by
    rw [le_div_iff₀ hEmax2pos]
    exact qd_small_c_modulus hc hc₀ hCπ hπ₁big hπ₂pos hMpos hc2
  have hpi0b2 : pi0 b₂ ≤ 2 * pi0 a₂ :=
    qd_pi0_two (by linarith [hP₀4, hP₀a₂]) ha₂b₂ (by linarith [ha₂b₂, hn₂])
  -- ================= the `QuadData` =================
  have hP1P2 : a₁ * a₂ / b₂ * b₂ = a₁ * a₂ := by field_simp
  have hMval : M = X / H := rfl
  have hMx : (X / (a₁ * a₂)) / (H / (a₁ * a₂)) = M := by rw [hMval]; field_simp
  have hgeomAll : ∀ e ∈ Aa, EdgeGeom F₂.fam (a₁ * a₂ / b₂) (H / (a₁ * a₂ / b₂ * b₂)) e := by
    intro e he
    obtain ⟨S, hSmem, hScard⟩ := hASAe e he
    have hSpos : 0 < (S.card : ℝ) := lt_of_lt_of_le hDOMfacpos hScard
    have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSpos)
    obtain ⟨p, hp⟩ := hSne
    obtain ⟨q, hq, hqe, -⟩ := hSmem p hp
    rw [← hqe, hP1P2]
    exact hedgeom q hq
  have hrelAll : ∀ e ∈ Aa, ∃ S : Finset ℕ, (∀ p ∈ S, IsPrimeIn (b₂ / 2) b₂ p) ∧
      c * pi0 b₂ ≤ (S.card : ℝ) ∧
      ∀ p ∈ S, EdgeRel k C (1 / (p : ℝ)) (H / (a₁ * a₂ / b₂ * b₂)) cpol e := by
    intro e he
    obtain ⟨S, hSmem, hScard⟩ := hASAe e he
    refine ⟨S, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q', hq', hq'eq, hpeq⟩ := hSmem p hp
      rw [← hpeq]
      have hmem : q'.1.2 ∈ Pr₂ := (Finset.mem_product.mp ((mem_DOM q').mp hq').1).2
      have hprime : q'.1.2.Prime := (Finset.mem_filter.mp hmem).2
      have hge : a₂ ≤ (q'.1.2 : ℝ) := hge_primesIn a₂ b₂ ha₂ ha₂b₂ q'.1.2 hmem
      exact ⟨hprime, by linarith [hge, hn₂, ha₂],
        hle_primesIn a₂ b₂ ha₂ ha₂b₂ q'.1.2 hmem⟩
    · have h1 : c * pi0 b₂ ≤
          ((c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
            - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M)) / (2 * ((M / 40) * (Cπ * pi0 a₁) ^ 2)) :=
        le_trans (mul_le_mul_of_nonneg_left hpi0b2 hc.le) hSb
      have h2 : ((c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M) ^ 2 / ((M / 40) * (Cπ * pi0 a₂))
            - (c₀ ^ 3 * pi0 a₁ * pi0 a₂ * M)) / (2 * ((M / 40) * (Cπ * pi0 a₁) ^ 2))
          ≤ (DOM.card : ℝ) / (2 * ((M / 40) * (Cπ * pi0 a₁) ^ 2)) :=
        div_le_div_of_nonneg_right hcard hEmax2pos.le
      linarith [h1, h2, hScard]
    · intro p hp
      obtain ⟨q', hq', hq'eq, hpeq⟩ := hSmem p hp
      rw [← hpeq, ← hq'eq, hP1P2]
      exact hedrel q' hq'
  refine ⟨a₁ * a₂ / b₂, b₂, hP1P2, ?_, ?_, le_refl _, ?_, ?_⟩
  · rw [le_div_iff₀ hb₂]; nlinarith [hb₁b₂]
  · rw [div_le_iff₀ hb₂]; nlinarith [ha₁, ha₂b₂]
  · linarith
  · refine ⟨⟨F₂.fam, cpol, ?_, ?_, ?_, ?_⟩, Aa, ?_, ?_, ?_⟩
    · rw [hP1P2]; exact F₂.isFam
    · rw [hP1P2]
      have h2 : c₂ * ((X / (a₁ * a₂)) / (H / (a₁ * a₂))) ≤ (F₂.fam.card : ℝ) := F₂.card_ge
      rw [hMx] at h2 ⊢
      exact le_trans (mul_le_mul_of_nonneg_right (le_trans hcc hcc₂) hMpos.le) h2
    · exact cpol_deg
    · intro x hx
      have h3 : H / (a₁ * a₂ / b₂ * b₂) = L₂ := by rw [hP1P2]
      rw [h3, cpol_corr x hx]
      exact le_trans (mul_le_mul_of_nonneg_right (le_trans hcc hcc₂) hL₂pos.le) (F₂.corr_ge x hx)
    · rw [hP1P2, hMx]; exact hAcardM
    · exact hgeomAll
    · exact hrelAll

end Work.BMF

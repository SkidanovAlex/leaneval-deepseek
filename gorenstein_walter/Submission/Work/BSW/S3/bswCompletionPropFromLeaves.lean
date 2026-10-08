import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Parity.bswParityProp
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.S3.S31setup

namespace Work.BSW.S3

open Subgroup Work.GW2

/-- A finite group acting fixed-point-freely has orbits of size `|A|`. -/
theorem card_orbit_eq_card_of_fixedPointFree {A α : Type} [Group A] [MulAction A α]
    (hfree : ∀ (g : A) (a : α), g • a = a → g = 1) (a : α) :
    Nat.card (MulAction.orbit A a) = Nat.card A := by
  have hinj : Function.Injective
      (fun g : A => (⟨g • a, MulAction.mem_orbit a g⟩ : MulAction.orbit A a)) := by
    intro g g' h
    have h1 : g • a = g' • a := Subtype.ext_iff.mp h
    have h2 : (g⁻¹ * g') • a = a := by rw [mul_smul, ← h1, inv_smul_smul]
    exact inv_mul_eq_one.mp (hfree (g⁻¹ * g') a h2)
  have hsurj : Function.Surjective
      (fun g : A => (⟨g • a, MulAction.mem_orbit a g⟩ : MulAction.orbit A a)) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

/-- A finite fixed-point-free action: `|A|` divides `|α|`. -/
theorem dvd_card_of_fixedPointFree {A α : Type} [Group A] [MulAction A α] [Finite A] [Finite α]
    (hfree : ∀ (g : A) (a : α), g • a = a → g = 1) : Nat.card A ∣ Nat.card α := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype (MulAction.orbitRel.Quotient A α) := Fintype.ofFinite _
  have hterm : ∀ ω : MulAction.orbitRel.Quotient A α,
      Nat.card (MulAction.orbit A (Quotient.out ω)) = Nat.card A :=
    fun ω => card_orbit_eq_card_of_fixedPointFree hfree (Quotient.out ω)
  have h1 : Nat.card α = ∑ ω : MulAction.orbitRel.Quotient A α, Nat.card A := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits A α), Nat.card_sigma]
    exact Finset.sum_congr rfl fun ω _ => hterm ω
  rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left _ _

/-- **Free actions give divisibility.**  A finite group acting on a finite type with a single
fixed point `b` and no other fixed point has `|A| ∣ |α| - 1`. -/
theorem dvd_card_sub_one_of_fixedPointFree {A α : Type} [Group A] [MulAction A α] [Finite A]
    [Finite α] (b : α) (hb : ∀ g : A, g • b = b)
    (hfree : ∀ (g : A), g ≠ 1 → ∀ a : α, g • a = a → a = b) :
    Nat.card A ∣ Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype {a : α // a ≠ b} := Fintype.ofFinite _
  haveI : Fintype {a : α // a = b} := Fintype.ofFinite _
  letI : MulAction A {a : α // a ≠ b} :=
    { smul := fun g a => ⟨g • a.1, by
        intro hgb
        exact a.2 (by rw [← inv_smul_smul g a.1, hgb, hb g⁻¹])⟩
      one_smul := fun a => Subtype.ext (one_smul A a.1)
      mul_smul := fun g g' a => Subtype.ext (mul_smul g g' a.1) }
  have hcard : Nat.card {a : α // a ≠ b} = Nat.card α - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : α => x = b), Fintype.card_subtype_eq]
  have hfree' : ∀ (g : A) (a : {a : α // a ≠ b}), g • a = a → g = 1 := by
    intro g a ha
    have ha' : g • a.1 = a.1 := Subtype.ext_iff.mp ha
    by_contra hg
    exact a.2 (hfree g hg a.1 ha')
  have hdvd := dvd_card_of_fixedPointFree (A := A) (α := {a : α // a ≠ b}) hfree'
  rwa [hcard] at hdvd

/-- Assembly step: from Bender §3.0–3.4 (`BSWExistsXProp`, `BSWS31Prop`, `BSWS32Prop`,
`BSWS34ArithProp`) applied with a sign `ε = ±1` and the corresponding order formula, extract an
element `x ∉ H^G` inverted by `t` together with the numerical conclusion of 3.4, expressed on the
centralizer `F = C_G(x)` and its normalizer. -/
private lemma bsw34_apply
    (hExistsX : Work.BSW.BSWExistsXProp) (h31 : Work.BSW.BSWS31Prop)
    (h32 : Work.BSW.BSWS32Prop) (h34 : Work.BSW.BSWS34ArithProp)
    {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (hH : BSWHyps2 G t s K) (h4 : 4 < Nat.card K) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hGZ : (Nat.card G : ℤ) = (2 * Nat.card K + ε) * (Nat.card K + ε) * (2 * Nat.card K)) :
    ∃ x : G, x ∉ HG t ∧ t⁻¹ * x * t = x⁻¹ ∧
      ((ε = 1 ∧ Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 * Nat.card K + 1 ∧
          K ≤ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) ∨
       (ε = -1 ∧ Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1 ∧
          Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
            2 * (Nat.card K - 1))) := by
  obtain ⟨x, hx, hinv, hineq⟩ := hExistsX G t s K ε hH h4 hε hGZ
  obtain ⟨_hF_comm, hF_odd, _hF_cent, _hF_TI, hF_inf_K, hM_eq, hFK_free, _hM_inv, hiFn,
    _hcop_idx, hcop_2k⟩ := h31 G t s K x hH hx hinv
  obtain ⟨h32a, h32b, h32c, h32d⟩ := h32 G t s K x hH hx hinv
  set F : Subgroup G := Subgroup.centralizer ({x} : Set G) with hFdef
  set M : Subgroup G := Subgroup.normalizer (F : Set G) with hMdef
  set f : ℕ := Nat.card F with hfdef
  set n : ℕ := Nat.card ↥(K ⊓ M) with hndef
  set m : ℕ := M.index with hmdef
  set I : ℕ := (Subgroup.centralizer ({t} : Set G)).index with hIdef
  set k : ℕ := Nat.card K with hkdef
  -- restatements in the `F`/`M` vocabulary
  have hF_odd' : Odd (Nat.card F) := hF_odd
  have hF_inf_K' : F ⊓ K = ⊥ := hF_inf_K
  have hM_eq' : M = F ⊔ (K ⊓ M) := hM_eq
  have hFK_free' : ∀ c ∈ K ⊓ M, c ≠ 1 → ∀ a ∈ F, c * a * c⁻¹ = a → a = 1 := hFK_free
  have hiFn' : Work.BSW.iFn G x = Nat.card F := hiFn
  have hkparity : Even k := by
    rw [hkdef]; exact Work.BSW.Parity.bswParityProp G t s K hH
  -- `|C_G(t)| = 2k`
  have hHcard : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * k := by
    rw [Work.BSW.centralizer_t_eq hH, Work.BSW.Api.card_sup_zpowers hH]
  have hcard_mul : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) *
      (Subgroup.centralizer ({t} : Set G)).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hG_eq : Nat.card G = 2 * k * I := by
    rw [← hcard_mul, hHcard, hIdef]
  -- `I = (2k+ε)(k+ε)`
  have hIeq : (I : ℤ) = (2 * k + ε) * (k + ε) := by
    have hGZ' : (Nat.card G : ℤ) = (2 * (k : ℤ) + ε) * ((k : ℤ) + ε) * (2 * (k : ℤ)) := by
      simpa only [← hkdef] using hGZ
    have h1 : (Nat.card G : ℤ) = 2 * (k : ℤ) * (I : ℤ) := by
      rw [hG_eq]; push_cast; ring
    have key : 2 * (k : ℤ) * (I : ℤ) = 2 * (k : ℤ) * ((2 * (k : ℤ) + ε) * ((k : ℤ) + ε)) := by
      rw [← h1, hGZ']; ring
    have h2k : (2 * (k : ℤ)) ≠ 0 := by
      have hpos : (0 : ℤ) < (k : ℤ) := by
        exact_mod_cast (by omega : 0 < k)
      exact mul_ne_zero (by norm_num) (ne_of_gt hpos)
    exact mul_left_cancel₀ h2k key
  -- `t ∈ M`
  have htM : t ∈ M := t_mem_normalizer_centralizer hH hx hinv
  have htKM : t ∈ K ⊓ M := ⟨Work.BSW.t_mem_K hH, htM⟩
  haveI : Nonempty ↥(K ⊓ M) := ⟨⟨t, htKM⟩⟩
  -- `|M| = f·n`
  have hd : F ⊓ (K ⊓ M) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyF, hyK, _hyM⟩
    rw [Subgroup.mem_bot]
    have h1 : y ∈ F ⊓ K := ⟨hyF, hyK⟩
    rw [hF_inf_K'] at h1
    exact Subgroup.mem_bot.mp h1
  have hsup : Nat.card ↥(F ⊔ (K ⊓ M)) = Nat.card ↥F * Nat.card ↥(K ⊓ M) :=
    Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot (H := F) (K := K ⊓ M) inf_le_right hd
  have hMcard : Nat.card ↥M = f * n := by
    have h1 : Nat.card ↥M = Nat.card ↥F * Nat.card ↥(K ⊓ M) := by
      conv_lhs => rw [hM_eq']
      rw [hsup]
    rw [h1, hfdef, hndef]
  -- `f·n·m = 2k·I`
  have hfnm : f * n * m = 2 * k * I := by
    have h1 : f * n * m = Nat.card G := by
      rw [← hMcard, hmdef]
      exact Subgroup.card_mul_index M
    rw [h1, hG_eq]
  -- `f ∣ I`
  have hdvd_fI : f ∣ I := by
    have hcop : Nat.Coprime f (2 * k) := by simpa only [hfdef, hkdef] using hcop_2k
    have hdvd : f ∣ 2 * k * I := by
      rw [← hG_eq]
      exact ⟨F.index, by rw [hfdef]; exact (Subgroup.card_mul_index F).symm⟩
    exact hcop.dvd_of_dvd_mul_left hdvd
  -- `n > 0`, `n` even, `n ∣ k`, `n ∣ f - 1`
  have hnpos : 0 < n := by rw [hndef]; exact Nat.card_pos
  have hneven : Even n := by
    have hle : Subgroup.zpowers t ≤ K ⊓ M := Subgroup.zpowers_le.mpr htKM
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ M) := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, Work.BSW.orderOf_t hH] at h
    exact even_iff_two_dvd.mpr (by rw [hndef]; exact hdvd)
  have hndvdk : n ∣ k := by
    rw [hndef, hkdef]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd_n_f1 : n ∣ f - 1 := by
    letI : MulAction ↥(K ⊓ M) ↥F :=
      MulAction.compHom ↥F (Subgroup.inclusion (show K ⊓ M ≤ M from inf_le_right))
    have hsmul : ∀ (c : ↥(K ⊓ M)) (b : ↥F),
        ((c • b : ↥F) : G) = (c : G) * (b : G) * (c : G)⁻¹ := fun c b => rfl
    have hfreeA : ∀ (g : ↥(K ⊓ M)), g ≠ 1 → ∀ a : ↥F, g • a = a → a = 1 := by
      intro g hg a ha
      have hgG : (g : G) ≠ 1 := fun h => hg (Subtype.ext h)
      have ha' : (g : G) * (a : G) * (g : G)⁻¹ = (a : G) := by
        have h := congrArg (fun z : ↥F => (z : G)) ha
        rwa [hsmul g a] at h
      exact Subtype.ext (hFK_free' (g : G) g.2 hgG (a : G) a.2 ha')
    have hb : ∀ g : ↥(K ⊓ M), g • (1 : ↥F) = 1 := by
      intro g
      apply Subtype.ext
      rw [hsmul g 1]
      simp
    have hres := dvd_card_sub_one_of_fixedPointFree (A := ↥(K ⊓ M)) (α := ↥F) 1 hb hfreeA
    simpa only [hndef, hfdef] using hres
  -- apply the arithmetic leaf
  have hchoice : (k : ℤ) * (k + 1 + 3 * ε) < (k + 1) * (f : ℤ) := by
    have h := hineq
    rw [hiFn'] at h
    exact h
  have h34hyps := h34 k f n m I ε h4 hkparity hε hIeq hF_odd' hneven hnpos hndvdk
    hdvd_n_f1 hfnm hdvd_fI hchoice h32a h32b h32c h32d
  refine ⟨x, hx, hinv, ?_⟩
  rcases h34hyps with ⟨hε1, hf_eq, hn_eq, _hI_eq⟩ | ⟨hεm1, hf_eq, hn_eq⟩
  · left
    refine ⟨hε1, hf_eq, ?_⟩
    show K ≤ M
    have hKM : K ⊓ M = K :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hn_eq.symm)
    exact hKM ▸ inf_le_right
  · right
    refine ⟨hεm1, hf_eq, ?_⟩
    show Nat.card ↥M = 2 * (Nat.card K - 1)
    rw [show Nat.card ↥M = f * n from hMcard, hf_eq, hn_eq]
    exact Nat.mul_comm _ _

theorem bswCompletionPropFromLeaves
    (hExistsX : Work.BSW.BSWExistsXProp) (h31 : Work.BSW.BSWS31Prop)
    (h32 : Work.BSW.BSWS32Prop) (h34 : Work.BSW.BSWS34ArithProp)
    (hCase1 : Work.BSW.BSWCase1Prop) (h35 : Work.BSW.BSWS35Prop)
    (h38 : Work.BSW.BSWS38Prop) :
    Work.BSW.BSWCompletionProp := by
  intro G _instGrp _instFin hSimple hnonab t s K hH h4 hG
  rcases hG with hGm | hGp
  · obtain ⟨x, hx, hinv, hd⟩ := bsw34_apply hExistsX h31 h32 h34 hH h4 (-1)
      (Or.inr rfl) (by
        rw [hGm]
        push_cast
        rw [Nat.cast_sub (show (1:ℕ) ≤ 2 * Nat.card K by omega),
            Nat.cast_sub (show (1:ℕ) ≤ Nat.card K by omega)]
        push_cast
        ring)
    rcases hd with ⟨hε1, _⟩ | ⟨_hεm1, hfk, hMn⟩
    · exact absurd hε1 (by norm_num)
    · obtain ⟨p, hp⟩ := h35 G t s K x hH h4 hGm hx hinv hfk hMn
      exact ⟨2 * Nat.card K - 1, Or.inl rfl, h38 G t s K x p hp⟩
  · obtain ⟨x, hx, hinv, hd⟩ := bsw34_apply hExistsX h31 h32 h34 hH h4 1
      (Or.inl rfl) (by
        rw [hGp]
        push_cast
        ring)
    rcases hd with ⟨_hε1, hfk, hKleM⟩ | ⟨hεm1, _⟩
    · exact ⟨2 * Nat.card K + 1, Or.inr rfl,
        hCase1 G t s K x hH h4 hx hinv hfk hKleM hGp⟩
    · exact absurd hεm1 (by norm_num)

end Work.BSW.S3


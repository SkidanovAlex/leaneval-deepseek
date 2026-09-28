import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.GamLoc.prim_has_dual
import Submission.Work.HP.NA.exists_lam_gcdMinors2
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.GamLoc.gcdMinors2_veronese

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `detL (Γ^{loc}_{x,y}(Q)) = Q ^ 2 / gcd(Q, 𝒢(x,y))`

Browning--Le Boudec--Sawin, "Lemma determinant mixed/local", local case.

The lattice `Γ = Γ^{loc}_{x,y}(Q) = latMod (ν x) Q ⊓ latMod (ν y) Q` is the kernel of the map
`a ↦ (⟪ν x, a⟫, ⟪ν y, a⟫) mod Q` from `ℤ^N` to `(ℤ/Q)^2`, so its index in `ℤ^N` (which equals
`detL Γ`, the covolume) is the cardinality of the image.  Writing `𝒢 = gcdMinors2 (ν x) (ν y)`
(which is `gcdMinors2 x y` by Lemma G, `gcdMinors2_veronese`), a Bézout dual vector `w` of `ν x`
splits `ℤ^N = ℤ w ⊕ latOrth (ν x)`, and the content of `⟨·, ν y⟩` on `latOrth (ν x)` is exactly
`𝒢 ℤ`; this gives `[ℤ^N : Γ] = Q * (Q / gcd(Q, 𝒢))`, as in the paper's Smith-normal-form proof.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

/-- The gcd of a finite set of integers is nonnegative. -/
lemma int_finset_gcd_nonneg {β : Type*} (s : Finset β) (f : β → ℤ) : 0 ≤ s.gcd f := by
  have h : |s.gcd f| = s.gcd f := by rw [Int.abs_eq_normalize, Finset.normalize_gcd]
  exact h ▸ abs_nonneg _

/-- Bézout for a finite family of integers. -/
lemma gcd_eq_sum_mul {β : Type*} [Fintype β] (f : β → ℤ) :
    ∃ lam : β → ℤ, ∑ b, lam b * f b = Finset.univ.gcd f := by
  classical
  by_cases h : ∀ b, f b = 0
  · exact ⟨0, by simp [Finset.gcd_eq_zero_iff.mpr (fun b _ => h b)]⟩
  · push Not at h
    obtain ⟨b₀, hb₀⟩ := h
    obtain ⟨lam, hlam⟩ :=
      Work.HP.GamLoc.prim_has_dual (fun b => f b / Finset.univ.gcd f)
        (Finset.gcd_div_eq_one (Finset.mem_univ b₀) hb₀)
    refine ⟨lam, ?_⟩
    have hfac : ∀ b, f b = (f b / Finset.univ.gcd f) * Finset.univ.gcd f :=
      fun b => (Int.ediv_mul_cancel (Finset.gcd_dvd (Finset.mem_univ b))).symm
    calc ∑ b, lam b * f b
        = ∑ b, lam b * ((f b / Finset.univ.gcd f) * Finset.univ.gcd f) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          conv_lhs => rw [hfac b]
      _ = (∑ b, lam b * (f b / Finset.univ.gcd f)) * Finset.univ.gcd f := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = 1 * Finset.univ.gcd f := by rw [hlam]
      _ = Finset.univ.gcd f := one_mul _

/-- The content of the pair `(c,d)` on the kernel of `c`, for `c` primitive. -/
lemma latOrth_dot_content {ι : Type*} [Fintype ι] (c d : ι → ℤ) (hc : IsPrim c) :
    (∀ b ∈ latOrth c, gcdMinors2 c d ∣ ∑ i, b i * d i)
      ∧ (∃ b ∈ latOrth c, ∑ i, b i * d i = gcdMinors2 c d) := by
  classical
  have hGnn : 0 ≤ gcdMinors2 c d := by
    rw [gcdMinors2]
    exact int_finset_gcd_nonneg _ _
  have hsingle : ∀ (i : ι) (v : ℤ) (e : ι → ℤ), ∑ k, (if k = i then v else 0) * e k = v * e i := by
    intro i v e
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- (A) the p-adic divisibility
  have hprime : ∀ (p : ℕ), Nat.Prime p → ∀ e : ℕ,
      ((p : ℤ) ^ e ∣ gcdMinors2 c d) → ∀ b ∈ latOrth c, (p : ℤ) ^ e ∣ ∑ i, b i * d i := by
    intro p hp e he b hb
    have hpz : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
    have hpc : ∃ i, ¬ ((p : ℤ) ∣ c i) := by
      by_contra hcon
      push Not at hcon
      have h1 : ((p : ℤ)) ∣ Finset.univ.gcd c := Finset.dvd_gcd fun i _ => hcon i
      rw [hc] at h1
      exact hpz.not_dvd_one h1
    obtain ⟨lam, hlam⟩ := Work.HP.NA.exists_lam_gcdMinors2 hp c d hpc he
    have hbc : ∑ i, b i * c i = 0 := by
      have h := Work.HP.mem_latOrth.mp hb
      rwa [Work.HP.pdot] at h
    have hkey : ((p : ℤ) ^ e ∣ ∑ i, b i * d i - lam * ∑ i, b i * c i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro i _
      have h1 : ((p : ℤ) ^ e ∣ b i * (d i - lam * c i)) := dvd_mul_of_dvd_right (hlam i) (b i)
      convert h1 using 1
      ring
    rwa [hbc, mul_zero, sub_zero] at hkey
  constructor
  · intro b hb
    rcases eq_or_ne (gcdMinors2 c d) 0 with hG0 | hG0
    · have hbc : ∑ i, b i * c i = 0 := by
        have h := Work.HP.mem_latOrth.mp hb
        rwa [Work.HP.pdot] at h
      have hx0 : ∑ i, b i * d i = 0 := by
        obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact Work.HP.isPrim_ne_zero hc (funext hcon)
        have hmin : ∀ i, c i₀ * d i = c i * d i₀ := by
          intro i
          have h := (Finset.gcd_eq_zero_iff.mp hG0) (i₀, i) (Finset.mem_univ _)
          linarith
        have hprod : c i₀ * (∑ i, b i * d i) = 0 := by
          calc c i₀ * (∑ i, b i * d i) = ∑ i, b i * (c i₀ * d i) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by ring
            _ = ∑ i, b i * (c i * d i₀) := Finset.sum_congr rfl fun i _ => by rw [hmin i]
            _ = (∑ i, b i * c i) * d i₀ := by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun i _ => by ring
            _ = 0 := by rw [hbc, zero_mul]
        exact (mul_eq_zero.mp hprod).resolve_left hi₀
      rw [hx0, hG0]
    · rw [← Int.natAbs_dvd_natAbs]
      refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr ?_
      intro p k hp hpk
      have hGk : ((p : ℤ) ^ k ∣ gcdMinors2 c d) := by
        have h1 : ((p ^ k : ℕ) : ℤ) ∣ ((gcdMinors2 c d).natAbs : ℤ) := by exact_mod_cast hpk
        rwa [Int.natAbs_of_nonneg hGnn, Nat.cast_pow] at h1
      have hx := hprime p hp k hGk b hb
      simpa using (Int.natAbs_dvd_natAbs.mpr hx)
  · rcases eq_or_ne (gcdMinors2 c d) 0 with hG0 | hG0
    · exact ⟨0, Submodule.zero_mem _, by rw [hG0]; simp⟩
    · obtain ⟨lam, hlam⟩ :=
        gcd_eq_sum_mul (β := ι × ι) (fun ij => c ij.1 * d ij.2 - c ij.2 * d ij.1)
      let m : ι × ι → ι → ℤ := fun ij =>
        (fun k => if k = ij.1 then c ij.2 else 0) - (fun k => if k = ij.2 then c ij.1 else 0)
      have hm_mem : ∀ ij, m ij ∈ latOrth c := by
        intro ij
        rw [Work.HP.mem_latOrth]
        show (∑ k, m ij k * c k) = 0
        have hsplit : ∀ k, m ij k * c k
            = (if k = ij.1 then c ij.2 else 0) * c k
              - (if k = ij.2 then c ij.1 else 0) * c k := by
          intro k
          simp only [m, Pi.sub_apply]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_sub_distrib,
          hsingle ij.1 (c ij.2) c, hsingle ij.2 (c ij.1) c]
        ring
      have hm_dot : ∀ ij, ∑ k, m ij k * d k = -(c ij.1 * d ij.2 - c ij.2 * d ij.1) := by
        intro ij
        have hsplit : ∀ k, m ij k * d k
            = (if k = ij.1 then c ij.2 else 0) * d k
              - (if k = ij.2 then c ij.1 else 0) * d k := by
          intro k
          simp only [m, Pi.sub_apply]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_sub_distrib,
          hsingle ij.1 (c ij.2) d, hsingle ij.2 (c ij.1) d]
        ring
      refine ⟨∑ ij, (-(lam ij)) • m ij, ?_, ?_⟩
      · exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (hm_mem ij)
      · calc ∑ k, (∑ ij, (-(lam ij)) • m ij) k * d k
            = ∑ k, ∑ ij, (-(lam ij)) * (m ij k * d k) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_apply, Finset.sum_mul]
              refine Finset.sum_congr rfl fun ij _ => ?_
              simp only [Pi.smul_apply, smul_eq_mul]
              ring
          _ = ∑ ij, ∑ k, (-(lam ij)) * (m ij k * d k) := Finset.sum_comm
          _ = ∑ ij, (-(lam ij)) * (∑ k, m ij k * d k) :=
              Finset.sum_congr rfl fun ij _ => by rw [Finset.mul_sum]
          _ = ∑ ij, (-(lam ij)) * (-(c ij.1 * d ij.2 - c ij.2 * d ij.1)) :=
              Finset.sum_congr rfl fun ij _ => by rw [hm_dot ij]
          _ = ∑ ij, lam ij * (c ij.1 * d ij.2 - c ij.2 * d ij.1) :=
              Finset.sum_congr rfl fun ij _ => by ring
          _ = gcdMinors2 c d := hlam

/-- Membership in `latMod c Q`, in terms of divisibility of the pairing. -/
private lemma mem_latMod_iff {ι : Type*} [Fintype ι] (c : ι → ℤ) (Q : ℕ) (a : ι → ℤ) :
    a ∈ latMod c Q ↔ (Q : ℤ) ∣ ∑ i, a i * c i := by
  rw [latMod, Submodule.mem_comap, Submodule.mem_span_singleton, Fintype.linearCombination_apply]
  simp only [smul_eq_mul]
  rw [dvd_def]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx, mul_comm]⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx, mul_comm]⟩

/-- Multiplication by `Q` lands in `latMod c Q`. -/
lemma smul_mem_latMod {ι : Type*} [Fintype ι] (c : ι → ℤ) (Q : ℕ) (a : ι → ℤ) :
    (Q : ℤ) • a ∈ latMod c Q := by
  rw [mem_latMod_iff]
  have h : (∑ i, ((Q : ℤ) • a) i * c i) = (Q : ℤ) * ∑ i, a i * c i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h]
  exact dvd_mul_right _ _

/-- The quotient of `ℤ^ι` by `latMod c Q` is cyclic of order `Q` (for `c` primitive, `Q ≥ 1`). -/
lemma card_quot_latMod {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℤ) (hc : IsPrim c)
    (Q : ℕ) (hQ : 1 ≤ Q) : Nat.card ((ι → ℤ) ⧸ latMod c Q) = Q := by
  classical
  haveI : NeZero Q := ⟨Nat.one_le_iff_ne_zero.mp hQ⟩
  obtain ⟨w, hw⟩ := Work.HP.GamLoc.prim_has_dual c hc
  let psi : (ι → ℤ) →ₗ[ℤ] ZMod Q :=
  { toFun := fun a => ((∑ i, a i * c i : ℤ) : ZMod Q)
    map_add' := fun a b => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Int.cast_add]
    map_smul' := fun n a => by
      have h1 : ∀ i, (n • a) i * c i = n * (a i * c i) := by
        intro i; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
      push_cast
      rw [zsmul_eq_mul]
      try simp only [id_eq]
      try ring }
  have hpsi : ∀ a : ι → ℤ, psi a = ((∑ i, a i * c i : ℤ) : ZMod Q) := fun a => rfl
  have hker : psi.ker = latMod c Q := by
    ext a
    rw [LinearMap.mem_ker, hpsi, mem_latMod_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsum : ∀ n : ℤ, (∑ i, (n • w) i * c i) = n := by
    intro n
    have h1 : ∀ i, (n • w) i * c i = n * (w i * c i) := by
      intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum, hw, mul_one]
  have hsurj : Function.Surjective psi := by
    intro u
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective u
    exact ⟨n • w, by rw [hpsi, hsum n, hn]⟩
  have : Nat.card ((ι → ℤ) ⧸ latMod c Q) = Nat.card (ZMod Q) := by
    rw [← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective psi hsurj).toEquiv
  rw [this, Nat.card_zmod]

/-- `latMod c Q ⊓ latMod d Q` has full rank. -/
lemma finrank_latMod_inf {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → ℤ) (Q : ℕ)
    (hQ : 1 ≤ Q) :
    Module.finrank ℤ ↥(latMod c Q ⊓ latMod d Q) = Fintype.card ι := by
  classical
  have hQz : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hQ)
  let f : (ι → ℤ) →ₗ[ℤ] ↥(latMod c Q ⊓ latMod d Q) :=
    (LinearMap.lsmul ℤ (ι → ℤ) (Q : ℤ)).codRestrict _
      (fun a => Submodule.mem_inf.mpr ⟨smul_mem_latMod c Q a, smul_mem_latMod d Q a⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (Q : ℤ) • x = (Q : ℤ) • y := congrArg Subtype.val hxy
    funext i
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact mul_left_cancel₀ hQz h2
  have h1 := f.finrank_le_finrank_of_injective hf
  have h2 : Module.finrank ℤ (ι → ℤ) = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℤ
  have h3 := Submodule.finrank_le (latMod c Q ⊓ latMod d Q)
  omega


/-- The Veronese map of a primitive vector is primitive. -/
private lemma isPrim_veronese {d n : ℕ} {x : Fin (n + 1) → ℤ} (hx : IsPrim x) :
    IsPrim (veronese d n x) := by
  classical
  rw [IsPrim] at hx ⊢
  by_contra hG
  have hGnn : 0 ≤ Finset.univ.gcd (fun m : Mon d n => veronese d n x m) :=
    int_finset_gcd_nonneg _ _
  have hnat : (Finset.univ.gcd (fun m : Mon d n => veronese d n x m)).natAbs ≠ 1 := by
    intro h1
    apply hG
    have h2 : |Finset.univ.gcd (fun m : Mon d n => veronese d n x m)| = 1 := by
      rw [Int.abs_eq_natAbs, h1]; norm_num
    rwa [abs_eq_self.mpr hGnn] at h2
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnat
  have hpz : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hpdvdZ : (p : ℤ) ∣ Finset.univ.gcd (fun m : Mon d n => veronese d n x m) := by
    have h := hpdvd
    have : (p : ℤ) ∣ (((Finset.univ.gcd (fun m : Mon d n => veronese d n x m)).natAbs : ℕ) : ℤ) := by
      exact_mod_cast h
    rwa [Int.natAbs_of_nonneg hGnn] at this
  have hxdvd : ∀ i : Fin (n + 1), (p : ℤ) ∣ x i := by
    intro i
    have h1 : (p : ℤ) ∣ veronese d n x (NA.monDi d n i) :=
      dvd_trans hpdvdZ (Finset.gcd_dvd (Finset.mem_univ _))
    rw [NA.veronese_monDi] at h1
    exact hpz.dvd_of_dvd_pow h1
  have h1 : (p : ℤ) ∣ Finset.univ.gcd x := Finset.dvd_gcd fun i _ => hxdvd i
  rw [hx] at h1
  exact hpz.not_dvd_one h1


/-- The relative index of `latMod c Q ⊓ latMod d Q` inside `latMod c Q` is `Q / gcd(Q, 𝒢(c,d))`.

The hypotheses supply a Bézout dual vector `w` for `c` and the two content facts about the pairing
with `d` on `latOrth c`. -/
lemma relIndex_latMod_inf {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → ℤ) (Q : ℕ)
    (hQ : 1 ≤ Q) (w : ι → ℤ) (hw : ∑ i, w i * c i = 1)
    (hdvd : ∀ b ∈ latOrth c, (Nat.gcd Q (gcdMinors2 c d).natAbs : ℤ) ∣ ∑ i, b i * d i)
    (hgen : ∃ b ∈ latOrth c, ∑ i, b i * d i = gcdMinors2 c d) :
    (latMod c Q ⊓ latMod d Q).toAddSubgroup.relIndex (latMod c Q).toAddSubgroup
      = Q / Nat.gcd Q (gcdMinors2 c d).natAbs := by
  classical
  set G : ℕ := Nat.gcd Q (gcdMinors2 c d).natAbs with hGdef
  let rho : ↥(latMod c Q) →ₗ[ℤ] ZMod Q :=
  { toFun := fun a => ((∑ i, (a : ι → ℤ) i * d i : ℤ) : ZMod Q)
    map_add' := fun a b => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, Int.cast_add]
    map_smul' := fun n a => by
      show ((∑ i, (n • (a : ι → ℤ)) i * d i : ℤ) : ZMod Q)
        = n • (((∑ i, (a : ι → ℤ) i * d i : ℤ)) : ZMod Q)
      have h1 : ∀ i, (n • (a : ι → ℤ)) i * d i = n * ((a : ι → ℤ) i * d i) := by
        intro i; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
      push_cast
      rw [zsmul_eq_mul]
      try simp only [id_eq]
      try ring }
  have hrho : ∀ a : ↥(latMod c Q), rho a = ((∑ i, (a : ι → ℤ) i * d i : ℤ) : ZMod Q) :=
    fun a => rfl
  have hker : rho.ker.toAddSubgroup
      = (latMod c Q ⊓ latMod d Q).toAddSubgroup.addSubgroupOf (latMod c Q).toAddSubgroup := by
    ext a
    show ((∑ i, (a : ι → ℤ) i * d i : ℤ) : ZMod Q) = 0
      ↔ ((a : ι → ℤ) ∈ latMod c Q ⊓ latMod d Q)
    rw [Submodule.mem_inf, mem_latMod_iff c Q (a : ι → ℤ), mem_latMod_iff d Q,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨fun h => ⟨(mem_latMod_iff c Q (a : ι → ℤ)).mp a.2, h⟩, fun h => h.2⟩
  -- the range is generated by `G`
  have hmemG : ((G : ℤ) : ZMod Q) ∈ rho.range := by
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, (G : ℤ) = x * gcdMinors2 c d + y * (Q : ℤ) := by
      have h := Nat.gcd_eq_gcd_ab (x := Q) (y := (gcdMinors2 c d).natAbs)
      have hcast : (((gcdMinors2 c d).natAbs : ℕ) : ℤ) = gcdMinors2 c d :=
        Int.natAbs_of_nonneg (int_finset_gcd_nonneg _ _)
      rw [hcast] at h
      refine ⟨Nat.gcdB Q (gcdMinors2 c d).natAbs, Nat.gcdA Q (gcdMinors2 c d).natAbs, ?_⟩
      rw [← hGdef] at h
      rw [h]; ring
    obtain ⟨b₀, hb₀mem, hb₀val⟩ := hgen
    have hb₀Γ : b₀ ∈ latMod c Q := by
      rw [mem_latMod_iff]
      have h : ∑ i, b₀ i * c i = 0 := by
        have hh := Work.HP.mem_latOrth.mp hb₀mem
        rwa [Work.HP.pdot] at hh
      rw [h]
      exact dvd_zero _
    refine ⟨x • ⟨b₀, hb₀Γ⟩, ?_⟩
    rw [map_smul, hrho]
    have h1 : ((∑ i, b₀ i * d i : ℤ) : ZMod Q) = ((gcdMinors2 c d : ℤ) : ZMod Q) := by
      rw [hb₀val]
    rw [h1]
    have h2 : ((G : ℤ) : ZMod Q) = x • ((gcdMinors2 c d : ℤ) : ZMod Q) := by
      rw [hxy]
      push_cast
      rw [zsmul_eq_mul]
      simp only [ZMod.natCast_self, mul_zero, add_zero]
    rw [← h2]
  have hrange : rho.range.toAddSubgroup = AddSubgroup.zmultiples ((G : ℤ) : ZMod Q) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [Submodule.mem_toAddSubgroup] at hv
      obtain ⟨a, rfl⟩ := hv
      rw [AddSubgroup.mem_zmultiples_iff]
      obtain ⟨s, hs⟩ : ∃ s : ℤ, ∑ i, (a : ι → ℤ) i * c i = (Q : ℤ) * s :=
        (mem_latMod_iff c Q (a : ι → ℤ)).mp a.2
      set b : ι → ℤ := (a : ι → ℤ) - s • ((Q : ℤ) • w) with hbdef
      have hbmem : b ∈ latOrth c := by
        rw [Work.HP.mem_latOrth, Work.HP.pdot]
        show (∑ i, b i * c i) = 0
        have hterm : ∀ i, b i * c i
            = (a : ι → ℤ) i * c i - s * (Q : ℤ) * (w i * c i) := by
          intro i
          simp only [hbdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hs, hw]
        ring
      have hsum : (∑ i, (a : ι → ℤ) i * d i)
          = (∑ i, b i * d i) + s * (Q : ℤ) * (∑ i, w i * d i) := by
        have hterm : ∀ i, (a : ι → ℤ) i * d i
            = b i * d i + s * (Q : ℤ) * (w i * d i) := by
          intro i
          simp only [hbdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.mul_sum]
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ∑ i, b i * d i = (G : ℤ) * k := hdvd b hbmem
      refine ⟨k, ?_⟩
      rw [hrho, hsum, hk]
      push_cast
      simp only [ZMod.natCast_self, mul_zero, add_zero]
      ring
    · intro v hv
      rw [AddSubgroup.mem_zmultiples_iff] at hv
      obtain ⟨k, rfl⟩ := hv
      rw [Submodule.mem_toAddSubgroup]
      exact Submodule.smul_mem _ k hmemG
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
  have hcard : Nat.card (↥(latMod c Q).toAddSubgroup ⧸ rho.ker.toAddSubgroup)
      = Nat.card (↥rho.range.toAddSubgroup) :=
    Nat.card_congr (LinearMap.quotKerEquivRange rho).toEquiv
  rw [hcard, hrange]
  rw [show ((G : ℤ) : ZMod Q) = ((G : ℕ) : ZMod Q) from by simp only [Int.cast_natCast]]
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe G (by omega : Q ≠ 0)]
  have hGdvdNat : G ∣ Q := by
    rw [hGdef]; exact Nat.gcd_dvd_left Q (gcdMinors2 c d).natAbs
  have hg : Q.gcd G = G :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right Q G) (Nat.dvd_gcd hGdvdNat (dvd_refl G))
  rw [hg]

/-- The tower: `[ℤ^ι : latMod c Q ⊓ latMod d Q] = Q * (Q / gcd(Q, 𝒢(c,d)))`. -/
lemma card_quot_inf {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → ℤ) (Q : ℕ)
    (hQ : 1 ≤ Q) (hc : IsPrim c)
    (hrel : (latMod c Q ⊓ latMod d Q).toAddSubgroup.relIndex (latMod c Q).toAddSubgroup
      = Q / Nat.gcd Q (gcdMinors2 c d).natAbs) :
    Nat.card ((ι → ℤ) ⧸ (latMod c Q ⊓ latMod d Q))
      = Q ^ 2 / Nat.gcd Q (gcdMinors2 c d).natAbs := by
  classical
  set G : ℕ := Nat.gcd Q (gcdMinors2 c d).natAbs with hGdef
  have hGdvd : G ∣ Q := by
    rw [hGdef]; exact Nat.gcd_dvd_left Q (gcdMinors2 c d).natAbs
  have hGpos : 0 < G := by
    rw [hGdef]; exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hmul := AddSubgroup.relIndex_mul_index
    (H := (latMod c Q ⊓ latMod d Q).toAddSubgroup) (K := (latMod c Q).toAddSubgroup)
    (fun x hx => hx.1)
  have hidx : (latMod c Q).toAddSubgroup.index = Q := by
    rw [AddSubgroup.index]
    exact card_quot_latMod c hc Q hQ
  have hidx2 : (latMod c Q ⊓ latMod d Q).toAddSubgroup.index
      = Nat.card ((ι → ℤ) ⧸ (latMod c Q ⊓ latMod d Q)) := rfl
  rw [hrel, hidx, hidx2] at hmul
  rw [← hmul]
  refine Nat.eq_of_mul_eq_mul_right hGpos ?_
  have hQ1 : Q / G * G = Q := Nat.div_mul_cancel hGdvd
  have hG2 : G ∣ Q ^ 2 := by
    rw [pow_two]; exact hGdvd.trans (dvd_mul_right Q Q)
  have hQ2 : Q ^ 2 / G * G = Q ^ 2 := Nat.div_mul_cancel hG2
  rw [hQ2]
  calc (Q / G * Q) * G = (Q / G * G) * Q := by ring
    _ = Q * Q := by rw [hQ1]
    _ = Q ^ 2 := by ring

/-- `detL` of a full-rank sublattice of `ℤ^ι` is the index, i.e. the cardinality of the quotient. -/
lemma detL_eq_card_quot {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    (h : Module.finrank ℤ L = Fintype.card ι) :
    detL L = (Nat.card ((ι → ℤ) ⧸ L) : ℝ) := by
  classical
  let bN : Module.Basis ι ℤ L := (Module.finBasisOfFinrankEq ℤ L h).reindex (Fintype.equivFin ι).symm
  let N : Matrix ι ι ℤ := Matrix.of fun i x => (bN i : ι → ℤ) x
  let M : Matrix ι ι ℝ := Matrix.of fun i x => ((bN i : ι → ℤ) x : ℝ)
  have hNmap : N.map (fun z : ℤ => (z : ℝ)) = M := by
    ext i j; simp [M, N]
  have hgram : (Matrix.of fun i j : ι =>
        ∑ x, (((bN i : ι → ℤ) x : ℝ) * ((bN j : ι → ℤ) x : ℝ))) = M * M.transpose := by
    ext i j
    simp [M, Matrix.mul_apply, Matrix.transpose_apply]
  have hbdet : (Pi.basisFun ℤ ι).det (Subtype.val ∘ ⇑bN) = N.det := by
    rw [Module.Basis.det_apply]
    have htm : (Pi.basisFun ℤ ι).toMatrix (Subtype.val ∘ ⇑bN) = N.transpose := by
      ext i j
      rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
      rfl
    rw [htm, Matrix.det_transpose]
  have hnat := Submodule.natAbs_det_basis_change (b := Pi.basisFun ℤ ι) L bN
  rw [hbdet] at hnat
  rw [Work.HP.Lat.detL_basis_gram L bN, hgram, Matrix.det_mul, Matrix.det_transpose, ← sq,
    Real.sqrt_sq_eq_abs, ← hnat]
  have hMdet : M.det = ((N.det : ℤ) : ℝ) := by
    rw [← hNmap]
    exact (Int.cast_det N).symm
  have habs : ((N.det.natAbs : ℕ) : ℝ) = |((N.det : ℤ) : ℝ)| :=
    (Nat.cast_natAbs (α := ℝ) N.det).trans Int.cast_abs
  rw [hMdet]
  exact habs.symm

/-- The index of `latMod c Q ⊓ latMod d Q` in `ℤ^ι`, for `c` primitive. -/
lemma card_quot_latMod_inf {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → ℤ) (hc : IsPrim c)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    Nat.card ((ι → ℤ) ⧸ (latMod c Q ⊓ latMod d Q))
      = Q ^ 2 / Nat.gcd Q (gcdMinors2 c d).natAbs := by
  classical
  obtain ⟨w, hw⟩ := Work.HP.GamLoc.prim_has_dual c hc
  obtain ⟨hcontent, hgen⟩ := latOrth_dot_content c d hc
  have hgdvd : (Nat.gcd Q (gcdMinors2 c d).natAbs : ℤ) ∣ gcdMinors2 c d := by
    have h1 : (Nat.gcd Q (gcdMinors2 c d).natAbs : ℤ)
        ∣ (((gcdMinors2 c d).natAbs : ℕ) : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right Q (gcdMinors2 c d).natAbs
    rwa [Int.natAbs_of_nonneg (a := gcdMinors2 c d) (int_finset_gcd_nonneg _ _)] at h1
  exact card_quot_inf c d Q hQ hc
    (relIndex_latMod_inf c d Q hQ w hw (fun b hb => hgdvd.trans (hcontent b hb)) hgen)

/-- **The local determinant** (Browning--Le Boudec--Sawin, "Lemma determinant mixed/local", local
case). -/
theorem detL_GamLoc (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (Q : ℕ) (hQ : 1 ≤ Q) :
    detL (GamLoc d n x y Q)
      = (Q : ℝ) ^ 2 / ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hcd : gcdMinors2 (veronese d n x) (veronese d n y) = gcdMinors2 x y :=
    Work.HP.GamLoc.gcdMinors2_veronese d n hd1 hn x y hx hy
  have hcard : Nat.card
        ((Mon d n → ℤ) ⧸ (latMod (veronese d n x) Q ⊓ latMod (veronese d n y) Q))
      = Q ^ 2 / Nat.gcd Q (gcdMinors2 (veronese d n x) (veronese d n y)).natAbs :=
    card_quot_latMod_inf _ _ (isPrim_veronese hx) Q hQ
  have hfin : Module.finrank ℤ
        ↥(latMod (veronese d n x) Q ⊓ latMod (veronese d n y) Q) = Fintype.card (Mon d n) :=
    finrank_latMod_inf _ _ Q hQ
  have hdet : detL (latMod (veronese d n x) Q ⊓ latMod (veronese d n y) Q)
      = (Nat.card ((Mon d n → ℤ) ⧸
          (latMod (veronese d n x) Q ⊓ latMod (veronese d n y) Q)) : ℝ) :=
    detL_eq_card_quot _ hfin
  rw [GamLoc, hdet, hcard, hcd]
  have hGdvd : Nat.gcd Q (gcdMinors2 x y).natAbs ∣ Q ^ 2 := by
    refine (Nat.gcd_dvd_left Q _).trans ?_
    rw [pow_two]; exact dvd_mul_right Q Q
  have hGne : ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) ≠ 0 := by
    have h : Nat.gcd Q (gcdMinors2 x y).natAbs ≠ 0 := by
      intro h0
      rw [Nat.gcd_eq_zero_iff] at h0
      omega
    exact_mod_cast h
  rw [Nat.cast_div hGdvd hGne, Nat.cast_pow]

end Work.HP

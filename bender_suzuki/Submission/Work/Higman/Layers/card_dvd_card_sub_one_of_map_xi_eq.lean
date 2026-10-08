import Mathlib
import Submission.Work.Higman.typeB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.Higman.Layers

open LeanEval.GroupTheory.Defs

variable {P : Type} [Group P] [Finite P]

/-- **`⟨ξ⟩` acts freely on `P ∖ {1}`.**  If every non-trivial power of `ξ` is fixed-point-free,
then the stabiliser of any `x ≠ 1` in the cyclic group `⟨ξ⟩` is trivial.

The only point to notice is that `⟨ξ⟩`-elements are *integral* powers `ξ ^ n`; reducing
`n` modulo `orderOf ξ` (which is positive because `MulAut P` is finite) produces a natural
exponent `k < orderOf ξ` with `ξ ^ k = ξ ^ n`, and `ξ ^ k ≠ 1` unless `k = 0`. -/
lemma stabilizer_zpowers_eq_bot (ξ : MulAut P)
    (hfpf : ∀ k : ℕ, ξ ^ k ≠ 1 → ∀ x : P, (ξ ^ k) x = x → x = 1)
    {x : P} (hx : x ≠ 1) :
    MulAction.stabilizer (Subgroup.zpowers ξ) x = ⊥ := by
  have hpos : 0 < orderOf ξ := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard ξ) Nat.card_pos
  have hmne : (orderOf ξ : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [MulAction.mem_stabilizer_iff] at hy
  have hyx : (y : MulAut P) x = x := hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
  set k : ℕ := (n % (orderOf ξ : ℤ)).toNat with hk
  have hk_lt : k < orderOf ξ := by
    have h1 : 0 ≤ n % (orderOf ξ : ℤ) := Int.emod_nonneg n hmne
    have h2 : n % (orderOf ξ : ℤ) < (orderOf ξ : ℤ) :=
      Int.emod_lt_of_pos n (by exact_mod_cast hpos)
    rw [hk]
    exact (Int.toNat_lt h1).mpr h2
  have hk_eq : ξ ^ k = (y : MulAut P) := by
    rw [← zpow_natCast ξ k, hk,
      Int.toNat_of_nonneg (Int.emod_nonneg n hmne), zpow_mod_orderOf, hn]
  have hfix : (ξ ^ k) x = x := by rw [hk_eq]; exact hyx
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exact Subtype.ext (by rw [← hk_eq, hk0, pow_zero]; rfl)
  · have hne : ξ ^ k ≠ 1 := by
      intro hc
      have hd : orderOf ξ ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hc
      exact absurd (Nat.le_of_dvd hkpos hd) (not_le.mpr hk_lt)
    exact absurd (hfpf k hne x hfix) hx

/-- Consequently every orbit of `⟨ξ⟩` on `P ∖ {1}` has cardinality `orderOf ξ`: the orbit
of `x ≠ 1` is in bijection with `⟨ξ⟩` by orbit–stabiliser. -/
lemma card_orbit_zpowers_of_fpf (ξ : MulAut P)
    (hfpf : ∀ k : ℕ, ξ ^ k ≠ 1 → ∀ x : P, (ξ ^ k) x = x → x = 1)
    {x : P} (hx : x ≠ 1) :
    Nat.card ↥(MulAction.orbit (Subgroup.zpowers ξ) x) = orderOf ξ := by
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers ξ) x)
  rw [Nat.card_prod, Nat.card_zpowers] at hos
  have hstab : Nat.card ↥(MulAction.stabilizer (Subgroup.zpowers ξ) x) = 1 := by
    rw [stabilizer_zpowers_eq_bot ξ hfpf hx, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (by
        rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩,
      ⟨1, Subgroup.mem_bot.mpr rfl⟩⟩
  rw [hstab, mul_one] at hos
  exact hos

/-- In the `FpfXi` setting `⟨ξ⟩` acts freely on `P \ {1}`: every non-trivial element has
exactly `q - 1` images under `⟨ξ⟩`.  Hence every `ξ`-invariant subgroup `H ≤ P` satisfies
`q - 1 ∣ |H| - 1`, where `q = |Z(P)|`.  (This is the group-side input used by the `C₄` analysis
in `H8/NOTES_c4_case_comm_A.md`, where only `ξ` itself — not all its powers — is
fixed-point-free.) -/
theorem card_dvd_card_sub_one_of_map_xi_eq {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    {H : Subgroup P} (hH : H.map (ξ : P →* P) = H) :
    (Nat.card ↥(Subgroup.center P) - 1) ∣ (Nat.card ↥H - 1) := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  rw [← hξ.order]
  -- membership in `H` is preserved by `ξ` and hence by all of `⟨ξ⟩`
  have hHiff : ∀ x : P, x ∈ H ↔ ξ x ∈ H := by
    intro x
    have h1 : ξ x ∈ H.map (ξ : P →* P) ↔ x ∈ H := by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := (ξ : MulAut P).injective hyx
        rwa [this] at hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [hH] at h1
    exact h1.symm
  have hKmem : ∀ g ∈ Subgroup.zpowers ξ, ∀ x : P, x ∈ H ↔ (g : MulAut P) x ∈ H := by
    let K' : Subgroup (MulAut P) :=
      { carrier := {g : MulAut P | ∀ x : P, x ∈ H ↔ (g : MulAut P) x ∈ H}
        one_mem' := by intro x; simp
        mul_mem' := by
          intro g h' hg hh x
          show x ∈ H ↔ (g : MulAut P) ((h' : MulAut P) x) ∈ H
          rw [← hg ((h' : MulAut P) x), ← hh x]
        inv_mem' := by
          intro g hg x
          have h1 := hg ((g : MulAut P).symm x)
          rw [MulEquiv.apply_symm_apply] at h1
          exact h1.symm }
    have hle : Subgroup.zpowers ξ ≤ K' := Subgroup.zpowers_le.mpr hHiff
    intro g hg
    exact hle hg
  -- the `⟨ξ⟩`-orbit of a point of `H` stays inside `H`
  have horbH : ∀ x ∈ H, ∀ a ∈ MulAction.orbit (Subgroup.zpowers ξ) x, a ∈ H := by
    intro x hx a ha
    rw [MulAction.mem_orbit_iff] at ha
    obtain ⟨g, hg⟩ := ha
    rw [← hg]
    exact (hKmem g g.2 x).mp hx
  -- `H ∖ {1}` as a finset
  set s : Finset P := Finset.univ.filter (fun x : P => x ∈ H ∧ x ≠ 1) with hs
  have hmem_s : ∀ x : P, x ∈ s ↔ x ∈ H ∧ x ≠ 1 := by
    intro x; rw [hs]; simp
  have hcard_s : s.card = Nat.card ↥H - 1 := by
    have hbij : s.card = (Finset.univ.filter (fun x : ↥H => x ≠ 1)).card := by
      refine Finset.card_bij (fun x hx => (⟨x, (hmem_s x).mp hx |>.1⟩ : ↥H)) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hc => (hmem_s x).mp hx |>.2 (Subtype.ext_iff.mp hc)
      · intro x hx y hy hxy
        simpa using congrArg (fun t : ↥H => (t : P)) hxy
      · intro y hy
        refine ⟨(y : P), (hmem_s _).mpr ⟨y.2, fun hc => ?_⟩, ?_⟩
        · exact (Finset.mem_filter.mp hy).2 (Subtype.ext hc)
        · exact Subtype.ext rfl
    rw [hbij]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ↥H)) (p := fun x : ↥H => x ≠ 1)
    have hone : (Finset.univ.filter (fun x : ↥H => ¬ x ≠ 1)).card = 1 := by
      have hset : (Finset.univ.filter (fun x : ↥H => ¬ x ≠ 1)) = {1} := by
        ext x; simp
      rw [hset]; simp
    rw [hone, Finset.card_univ] at hsplit
    have hHcard : Nat.card ↥H = Fintype.card ↥H := Nat.card_eq_fintype_card
    omega
  rw [← hcard_s]
  -- the orbits partition `H ∖ {1}` and each has cardinality `orderOf ξ`
  rw [Finset.card_eq_sum_card_image (f := fun x : P => MulAction.orbit (Subgroup.zpowers ξ) x) s]
  apply Finset.dvd_sum
  intro b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hxH, hx1⟩ := (hmem_s x).mp hx
  -- the fibre of the orbit map over `orbit x` is the whole orbit
  have hset : (s.filter (fun a : P =>
        MulAction.orbit (Subgroup.zpowers ξ) a = MulAction.orbit (Subgroup.zpowers ξ) x)) =
      ((MulAction.orbit (Subgroup.zpowers ξ) x : Set P)).toFinset := by
    ext a
    simp only [Finset.mem_filter, Set.mem_toFinset, MulAction.orbit_eq_iff, hmem_s,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, ha⟩; exact ha
    · intro ha
      refine ⟨⟨horbH x hxH a ha, ?_⟩, ha⟩
      intro hcon
      rw [hcon] at ha
      rw [MulAction.mem_orbit_iff] at ha
      obtain ⟨γ, hγ⟩ := ha
      exact hx1 (by
        calc x = γ⁻¹ • (γ • x) := by rw [inv_smul_smul]
          _ = γ⁻¹ • (1 : P) := by rw [← hγ]
          _ = 1 := by simp)
  have hfib : (s.filter (fun a : P =>
        MulAction.orbit (Subgroup.zpowers ξ) a = MulAction.orbit (Subgroup.zpowers ξ) x)).card =
      orderOf ξ := by
    rw [hset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact card_orbit_zpowers_of_fpf ξ hξ.fpf hx1
  rw [hfib]

end Work.Higman.Layers

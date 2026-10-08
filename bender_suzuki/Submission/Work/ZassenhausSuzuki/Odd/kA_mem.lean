import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_hall
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_conj_of_prime_dvd
import Submission.Work.ZassenhausSuzuki.QSZPowFour
import Submission.Work.ZassenhausSuzuki.Odd.no_inverting_pair_of_suzuki2_q2
import Submission.Work.ZassenhausSuzuki.Odd.card_le_four_of_unique_involution
import Submission.Work.ThmF.Bender.involutionMemConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.kA_mem`

Huppert–Blackburn XI, Lemma 11.4 (Suzuki 1962, Prop. 14/15): for `A = C_G(x)` the centraliser of
a non-identity strongly real element which is not an involution (i.e. `A ∈ ℱ`, the family
`Work.ZassenhausSuzuki.Odd.IsCZ`), the index `kA A = [N_G(A) : A]` is `2` or `4`.

The proof follows HB 11.4:

* `A` is abelian of odd order and `C_G(a) = A` for every `a ∈ A#` (Suzuki's Prop. 14,
  `Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real`, packaged as `isCZ_basic`).
* `A` is a Hall subgroup of `G` (`isCZ_hall`), so a fortiori of `N = N_G(A)`, and by
  Schur–Zassenhaus `N = A ⋊ 𝔎` for a complement `𝔎` with `|𝔎| = kA A`.
* `𝔎` acts fixed-point-freely on `A`, hence any two involutions of `𝔎` both induce inversion on
  `A` and are therefore equal: `𝔎` has a unique involution `z`, which is central.
* Writing `α = a k` for the involution `α` exhibiting `x` as strongly real, one gets an explicit
  involution `z = a⁻¹α ∈ 𝔎`; since `z ∈ Z(𝔎)`, we have `𝔎 ≤ C_G(z)`, and any involution of `G` is
  conjugate into `H`, where its centraliser lies in the Suzuki 2-group `Q`.
* Hence `𝔎` is isomorphic to a subgroup `R ≤ Q` of the Suzuki 2-group, with a unique involution.
  A subgroup of a `q²`-type Suzuki 2-group with a unique involution has order at most `4`
  (`card_le_four_of_unique_involution` via `no_inverting_pair_of_suzuki2_q2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Elementary structure of a member of `ℱ` -/

/-- A member of `ℱ` is non-trivial. -/
theorem isCZ_ne_bot {A : Subgroup G} (hA : IsCZ A) : A ≠ ⊥ := by
  obtain ⟨x, -, hx1, -, hAx⟩ := hA
  intro hbot
  have hx : x ∈ A := by
    rw [← hAx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hx))

/-- A member of `ℱ` is self-centralizing. -/
theorem centralizer_coe_eq_of_isCZ (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A) :
    Subgroup.centralizer (A : Set G) = A := by
  obtain ⟨hmul, -, hcent⟩ := isCZ_basic h hA
  haveI : IsMulCommutative ↥A := hmul
  refine le_antisymm (fun g hg => ?_) (fun a ha => ?_)
  · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (isCZ_ne_bot hA)
    have hga : g ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hg (a : G) a.2).symm
    have ha1' : (a : G) ≠ 1 := fun hc => ha1 (Subtype.ext hc)
    rw [(hcent (a : G) a.2 ha1').2] at hga
    exact hga
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (congrArg Subtype.val (mul_comm' (M := ↥A) ⟨a, ha⟩ ⟨b, hb⟩)).symm

/-- `y * x⁻¹ = x⁻¹ * y ↔ y * x = x * y`. -/
private lemma commute_inv_iff' {y x : G} : y * x⁻¹ = x⁻¹ * y ↔ y * x = x * y := by
  constructor
  · intro h
    have h1 : x * (y * x⁻¹) * x = x * (x⁻¹ * y) * x := by rw [h]
    rw [show x * (y * x⁻¹) * x = x * y from by group,
      show x * (x⁻¹ * y) * x = y * x from by group] at h1
    exact h1.symm
  · intro h
    have h1 : x⁻¹ * (x * y) * x⁻¹ = x⁻¹ * (y * x) * x⁻¹ := by rw [h]
    rwa [show x⁻¹ * (x * y) * x⁻¹ = y * x⁻¹ from by group,
      show x⁻¹ * (y * x) * x⁻¹ = x⁻¹ * y from by group] at h1

/-- A fixed-point-free automorphism of order dividing two of an abelian group is inversion. -/
private lemma eq_inv_of_fpf_sq_id {M : Type*} [Group M] [IsMulCommutative M] (φ : M →* M)
    (h2 : ∀ x, φ (φ x) = x) (hf : ∀ x, φ x = x → x = 1) : ∀ x, φ x = x⁻¹ := by
  intro x
  have hfix : φ (φ x * x) = φ x * x := by
    rw [map_mul, h2]
    exact mul_comm' x (φ x)
  exact eq_inv_of_mul_eq_one_left (hf _ hfix)

/-- **The key computation of HB 11.4.**  Let `A ∈ ℱ` and let `u, v ∈ N_G(A)` be elements outside
`A` with `u², v² ∈ A`.  Then `u v⁻¹ ∈ A`:  conjugation by `u` and by `v` is a fixed-point-free
automorphism of exponent two of the abelian group `A`, hence inversion, so `u v⁻¹` acts
trivially, i.e. lies in `C_G(A) = A`. -/
theorem mem_mul_inv_mem_of_mem_normalizer (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A)
    {u v : G} (huN : u ∈ Subgroup.normalizer (A : Set G))
    (hvN : v ∈ Subgroup.normalizer (A : Set G)) (huA : u ∉ A) (hvA : v ∉ A)
    (hu2 : u * u ∈ A) (hv2 : v * v ∈ A) : u * v⁻¹ ∈ A := by
  obtain ⟨hmul, -, hcent⟩ := isCZ_basic h hA
  haveI : IsMulCommutative ↥A := hmul
  have hcen : Subgroup.centralizer (A : Set G) = A := centralizer_coe_eq_of_isCZ h hA
  have key : ∀ w : G, w ∈ Subgroup.normalizer (A : Set G) → w ∉ A → w * w ∈ A →
      ∀ a ∈ A, w * a * w⁻¹ = a⁻¹ := by
    intro w hwN hwA hw2 a ha
    have hmap : ∀ b ∈ A, w * b * w⁻¹ ∈ A := fun b hb => (Subgroup.mem_normalizer_iff.mp hwN b).mp hb
    let φ : ↥A →* ↥A :=
      { toFun := fun b => ⟨w * (b : G) * w⁻¹, hmap b b.2⟩
        map_one' := by ext; simp
        map_mul' := by intro b c; ext; simp only [Subgroup.coe_mul]; group }
    have hφ2 : ∀ b : ↥A, φ (φ b) = b := by
      intro b
      have hww : w * w ∈ Subgroup.centralizer (A : Set G) := by rw [hcen]; exact hw2
      have hcomm : (b : G) * (w * w) = (w * w) * (b : G) :=
        Subgroup.mem_centralizer_iff.mp hww (b : G) b.2
      ext
      show w * (w * (b : G) * w⁻¹) * w⁻¹ = (b : G)
      calc w * (w * (b : G) * w⁻¹) * w⁻¹ = (w * w) * (b : G) * (w * w)⁻¹ := by group
        _ = (b : G) := by rw [← hcomm]; group
    have hφf : ∀ b : ↥A, φ b = b → b = 1 := by
      intro b hb
      have hbG : w * (b : G) * w⁻¹ = (b : G) := congrArg Subtype.val hb
      by_contra hbne
      have hbne' : (b : G) ≠ 1 := fun hc => hbne (Subtype.ext hc)
      have hmem : w ∈ Subgroup.centralizer ({(b : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc w * (b : G) = (w * (b : G) * w⁻¹) * w := by group
          _ = (b : G) * w := by rw [hbG]
      rw [(hcent (b : G) b.2 hbne').2] at hmem
      exact hwA hmem
    have h2 : w * (a : G) * w⁻¹ = (a : G)⁻¹ := by
      have h1 := eq_inv_of_fpf_sq_id φ hφ2 hφf ⟨a, ha⟩
      have h3 := congrArg Subtype.val h1
      simpa [φ] using h3
    exact h2
  have hu := key u huN huA hu2
  have hv := key v hvN hvA hv2
  rw [← hcen, Subgroup.mem_centralizer_iff]
  intro a ha
  have hv' : v⁻¹ * a * v = a⁻¹ := by
    have h1 : (v * a * v⁻¹)⁻¹ = a := by rw [hv a ha, inv_inv]
    calc v⁻¹ * a * v = v⁻¹ * (v * a * v⁻¹)⁻¹ * v := by rw [h1]
      _ = a⁻¹ := by group
  have hconj : (u * v⁻¹) * a * (u * v⁻¹)⁻¹ = a := by
    calc (u * v⁻¹) * a * (u * v⁻¹)⁻¹ = u * (v⁻¹ * a * v) * u⁻¹ := by group
      _ = u * a⁻¹ * u⁻¹ := by rw [hv']
      _ = (u * a * u⁻¹)⁻¹ := by group
      _ = (a⁻¹)⁻¹ := by rw [hu a ha]
      _ = a := inv_inv a
  calc a * (u * v⁻¹) = ((u * v⁻¹) * a * (u * v⁻¹)⁻¹) * (u * v⁻¹) := by rw [hconj]
    _ = (u * v⁻¹) * a := by group

/-! ## The main theorem -/

theorem kA_mem (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t)
    {A : Subgroup G} (hA : Work.ZassenhausSuzuki.Odd.IsCZ A) :
    Work.ZassenhausSuzuki.Odd.kA A = 2 ∨ Work.ZassenhausSuzuki.Odd.kA A = 4 := by
  classical
  have hAcz : IsCZ A := hA
  obtain ⟨hmulA, hoddA, hcentA⟩ := isCZ_basic h hA
  haveI : IsMulCommutative ↥A := hmulA
  have hAne : A ≠ ⊥ := isCZ_ne_bot hAcz
  have hcen : Subgroup.centralizer (A : Set G) = A := centralizer_coe_eq_of_isCZ h hAcz
  -- the strongly real element `x` and the involution `a₀` exhibiting it
  obtain ⟨x, hsr, hx1, hx2, hAx⟩ := hA
  obtain ⟨a₀, b₀, ha₀, hb₀, hab⟩ := hsr
  have hxmem : x ∈ A := by
    rw [← hAx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀
  have hαx : a₀ * x * a₀⁻¹ = x⁻¹ := by
    rw [← hab]
    calc a₀ * (a₀ * b₀) * a₀⁻¹ = (a₀ * a₀) * (b₀ * a₀⁻¹) := by group
      _ = b₀ * a₀ := by rw [ha₀, ha₀inv, one_mul]
      _ = (a₀ * b₀)⁻¹ := by rw [mul_inv_rev, ha₀inv, inv_eq_of_mul_eq_one_right hb₀]
  -- `a₀` normalises `C_G(x) = A`
  have hstep : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      a₀ * y * a₀⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hax : a₀⁻¹ * x * a₀ = x⁻¹ := by simpa [ha₀inv] using hαx
    have hax' : a₀ * x⁻¹ * a₀⁻¹ = x := by
      have h1 := congrArg Inv.inv hαx
      simpa [mul_inv_rev, inv_inv, mul_assoc] using h1
    have hyx' : y * x⁻¹ = x⁻¹ * y := commute_inv_iff'.mpr hyx
    calc (a₀ * y * a₀⁻¹) * x = a₀ * (y * (a₀⁻¹ * x * a₀)) * a₀⁻¹ := by group
      _ = a₀ * (y * x⁻¹) * a₀⁻¹ := by rw [hax]
      _ = a₀ * (x⁻¹ * y) * a₀⁻¹ := by rw [hyx']
      _ = (a₀ * x⁻¹ * a₀⁻¹) * (a₀ * y * a₀⁻¹) := by group
      _ = x * (a₀ * y * a₀⁻¹) := by rw [hax']
  have hαN : a₀ ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← hAx]
    exact ⟨hstep y, fun hy => by
      have h1 := hstep (a₀ * y * a₀⁻¹) hy
      have h2 : a₀ * (a₀ * y * a₀⁻¹) * a₀⁻¹ = y := by
        calc a₀ * (a₀ * y * a₀⁻¹) * a₀⁻¹ = (a₀ * a₀) * y * (a₀⁻¹ * a₀⁻¹) := by group
          _ = y := by simp [ha₀, ha₀inv]
      rw [h2] at h1
      exact h1⟩
  have hαA : a₀ ∉ A := by
    intro hc
    have hcomm : a₀ * x = x * a₀ :=
      congrArg Subtype.val (mul_comm' (M := ↥A) ⟨a₀, hc⟩ ⟨x, hxmem⟩)
    have h1 : a₀ * x * a₀⁻¹ = x := by
      calc a₀ * x * a₀⁻¹ = (x * a₀) * a₀⁻¹ := by rw [hcomm]
        _ = x := by group
    rw [hαx] at h1
    exact hx2 (by
      calc x * x = x * x⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel x)
  -- Schur–Zassenhaus: `N_G(A) = A ⋊ 𝔎`
  let NN : Subgroup G := Subgroup.normalizer (A : Set G)
  let AA : Subgroup ↥NN := A.subgroupOf NN
  have hAN : A ≤ NN := Subgroup.le_normalizer
  haveI : AA.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mpr le_rfl
  have hcopA : Nat.Coprime (Nat.card ↥A) (kA A) := by
    have h2 : Nat.Coprime (Nat.card ↥A) A.index := isCZ_hall h hAcz
    have hrel : A.relIndex NN = kA A := rfl
    have hmul : A.relIndex NN * NN.index = A.index := Subgroup.relIndex_mul_index hAN
    rw [hrel] at hmul
    exact Nat.Coprime.coprime_dvd_right ⟨NN.index, hmul.symm⟩ h2
  have hcop : Nat.Coprime (Nat.card ↥AA) AA.index := by
    have hcard : Nat.card ↥AA = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    have hidx : AA.index = kA A := rfl
    rw [hcard, hidx]
    exact hcopA
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := AA) hcop
  let K' : Subgroup G := K.map NN.subtype
  have hKcard : Nat.card ↥K = kA A := by
    have h1 : AA.index = Nat.card ↥K := hK.symm.index_eq_card
    rw [← h1]
    rfl
  have hK'le : K' ≤ NN := Subgroup.map_subtype_le K
  have hK'card : Nat.card ↥K' = kA A := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective NN), hKcard]
  have hdisj : AA ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
  have hdisjG : A ⊓ K' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro gg hg
    obtain ⟨hgA, hgK⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hgK
    have hkG : (k : G) = gg := hkg
    have hkA : k ∈ AA := by
      rw [Subgroup.mem_subgroupOf]
      rw [hkG]
      exact hgA
    have h1 : k ∈ AA ⊓ K := Subgroup.mem_inf.mpr ⟨hkA, hk⟩
    rw [hdisj] at h1
    have hk1 : k = 1 := Subgroup.mem_bot.mp h1
    rw [← hkg, hk1]
    simp
  -- an explicit involution `z ∈ 𝔎`
  have ha₀NN : a₀ ∈ NN := hαN
  have hmem_top : (⟨a₀, ha₀NN⟩ : ↥NN) ∈ AA ⊔ K := by
    rw [hK.sup_eq_top]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_left] at hmem_top
  obtain ⟨p, hp, kk, hkk, hpk⟩ := hmem_top
  have hpkG : ((p : ↥NN) : G) * ((kk : ↥NN) : G) = a₀ := by
    have h1 := congrArg Subtype.val hpk
    simpa using h1
  have hkkeq : ((kk : ↥NN) : G) = ((p : ↥NN) : G)⁻¹ * a₀ := by
    rw [← hpkG]
    group
  have hzmem : ((kk : ↥NN) : G) ∈ K' := Subgroup.mem_map.mpr ⟨kk, hkk, rfl⟩
  have hz1 : ((kk : ↥NN) : G) ≠ 1 := by
    intro hc
    apply hαA
    have hpA : ((p : ↥NN) : G) ∈ A := Subgroup.mem_subgroupOf.mp hp
    have h1 : a₀ = ((p : ↥NN) : G) := by rw [← hpkG, hc, mul_one]
    rw [h1]
    exact hpA
  have hzsqA : ((kk : ↥NN) : G) * ((kk : ↥NN) : G) ∈ A := by
    have hpA : ((p : ↥NN) : G) ∈ A := Subgroup.mem_subgroupOf.mp hp
    have hconjA : a₀ * ((p : ↥NN) : G)⁻¹ * a₀⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hαN ((p : ↥NN) : G)⁻¹).mp (A.inv_mem hpA)
    rw [hkkeq]
    have h1 : ((p : ↥NN) : G)⁻¹ * a₀ * (((p : ↥NN) : G)⁻¹ * a₀)
        = ((p : ↥NN) : G)⁻¹ * (a₀ * ((p : ↥NN) : G)⁻¹ * a₀⁻¹) := by
      calc ((p : ↥NN) : G)⁻¹ * a₀ * (((p : ↥NN) : G)⁻¹ * a₀)
          = ((p : ↥NN) : G)⁻¹ * (a₀ * ((p : ↥NN) : G)⁻¹ * a₀⁻¹) * (a₀ * a₀) := by group
        _ = ((p : ↥NN) : G)⁻¹ * (a₀ * ((p : ↥NN) : G)⁻¹ * a₀⁻¹) := by rw [ha₀, mul_one]
    rw [h1]
    exact A.mul_mem (A.inv_mem hpA) hconjA
  have hzsq : ((kk : ↥NN) : G) * ((kk : ↥NN) : G) = 1 := by
    have hzsqK : ((kk : ↥NN) : G) * ((kk : ↥NN) : G) ∈ K' := K'.mul_mem hzmem hzmem
    have h2 : ((kk : ↥NN) : G) * ((kk : ↥NN) : G) ∈ A ⊓ K' := ⟨hzsqA, hzsqK⟩
    rw [hdisjG] at h2
    exact Subgroup.mem_bot.mp h2
  -- `𝔎` has at most one involution
  have huniqK' : ∀ u v : G, u ∈ K' → v ∈ K' → u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u = v := by
    intro u v hu hv hu2 hv2 hu1 hv1
    have huN : u ∈ Subgroup.normalizer (A : Set G) := hK'le hu
    have hvN : v ∈ Subgroup.normalizer (A : Set G) := hK'le hv
    have huA : u ∉ A := by
      intro hc
      have h2 : u ∈ A ⊓ K' := ⟨hc, hu⟩
      rw [hdisjG] at h2
      exact hu1 (Subgroup.mem_bot.mp h2)
    have hvA : v ∉ A := by
      intro hc
      have h2 : v ∈ A ⊓ K' := ⟨hc, hv⟩
      rw [hdisjG] at h2
      exact hv1 (Subgroup.mem_bot.mp h2)
    have hmem : u * v⁻¹ ∈ A :=
      mem_mul_inv_mem_of_mem_normalizer h hAcz huN hvN huA hvA
        (by rw [hu2]; exact A.one_mem) (by rw [hv2]; exact A.one_mem)
    have hmem' : u * v⁻¹ ∈ K' := K'.mul_mem hu (K'.inv_mem hv)
    have h2 : u * v⁻¹ ∈ A ⊓ K' := ⟨hmem, hmem'⟩
    rw [hdisjG] at h2
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h2)
  -- `z` is central in `𝔎`
  have hzcenter : ∀ y ∈ K', y * ((kk : ↥NN) : G) = ((kk : ↥NN) : G) * y := by
    intro y hy
    have hyzy : y * ((kk : ↥NN) : G) * y⁻¹ ∈ K' :=
      K'.mul_mem (K'.mul_mem hy hzmem) (K'.inv_mem hy)
    have hsq : (y * ((kk : ↥NN) : G) * y⁻¹) * (y * ((kk : ↥NN) : G) * y⁻¹) = 1 := by
      have e : (y * ((kk : ↥NN) : G) * y⁻¹) * (y * ((kk : ↥NN) : G) * y⁻¹)
          = y * (((kk : ↥NN) : G) * ((kk : ↥NN) : G)) * y⁻¹ := by group
      rw [e, hzsq]
      group
    have hne : y * ((kk : ↥NN) : G) * y⁻¹ ≠ 1 := by
      intro hc
      apply hz1
      calc ((kk : ↥NN) : G) = y⁻¹ * (y * ((kk : ↥NN) : G) * y⁻¹) * y := by group
        _ = y⁻¹ * 1 * y := by rw [hc]
        _ = 1 := by group
    have h3 := huniqK' (y * ((kk : ↥NN) : G) * y⁻¹) ((kk : ↥NN) : G) hyzy hzmem
      hsq hzsq hne hz1
    calc y * ((kk : ↥NN) : G) = (y * ((kk : ↥NN) : G) * y⁻¹) * y := by group
      _ = ((kk : ↥NN) : G) * y := by rw [h3]
  have hK'cent : K' ≤ Subgroup.centralizer ({((kk : ↥NN) : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzcenter y hy
  -- `z` is conjugate into `H`, so `𝔎` is isomorphic to a subgroup of the Suzuki 2-group `Q`
  have hz2order : orderOf ((kk : ↥NN) : G) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
  obtain ⟨g, hg⟩ := Work.ThmF.Bender.involutionMemConj h.hsplit.stronglyEmbedded hz2order
  rw [Submission.Blueprint.conj, Subgroup.mem_map] at hg
  obtain ⟨u, huH, huconj⟩ := hg
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at huconj
  have hu2 : orderOf u = 2 := by
    rw [← Work.ThmF.Bender.orderOf_conj_eq g u, huconj, hz2order]
  have hcentu : Subgroup.centralizer ({u} : Set G) ≤ Q :=
    Work.ZassenhausSuzuki.centralizer_le_Q_of_mem_involutions h.hsplit h.hzass h.h2 ⟨huH, hu2⟩
  have hCz : Subgroup.centralizer ({((kk : ↥NN) : G)} : Set G) ≤ Submission.Blueprint.conj g Q := by
    have h1 : Subgroup.centralizer ({((kk : ↥NN) : G)} : Set G)
        = Submission.Blueprint.conj g (Subgroup.centralizer ({u} : Set G)) := by
      rw [← huconj]
      exact (conj_conj_centralizer_singleton g u).symm
    rw [h1]
    exact Subgroup.map_mono hcentu
  have hK'conjQ : K' ≤ Submission.Blueprint.conj g Q := hK'cent.trans hCz
  let R : Subgroup G := Submission.Blueprint.conj g⁻¹ K'
  have hRQ : R ≤ Q := by
    intro w hw
    have hw' : w ∈ K'.map (MulAut.conj g⁻¹).toMonoidHom := hw
    rw [Subgroup.mem_map] at hw'
    obtain ⟨y, hy, hyw⟩ := hw'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyw
    have hyQ : g⁻¹ * y * g ∈ Q := by
      have h1 : y ∈ Q.map (MulAut.conj g).toMonoidHom := hK'conjQ hy
      rw [Subgroup.mem_map] at h1
      obtain ⟨w2, hw2, hw2y⟩ := h1
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hw2y
      have h2 : w2 = g⁻¹ * y * g := by rw [← hw2y]; group
      rw [← h2]
      exact hw2
    rw [← hyw]
    simpa using hyQ
  have hRcard : Nat.card ↥R = kA A := by
    have h1 : Nat.card ↥R = Nat.card ↥K' :=
      Subgroup.card_map_of_injective (K := K') (f := (MulAut.conj g⁻¹).toMonoidHom)
        ((MulAut.conj g⁻¹).injective)
    rw [h1, hK'card]
  have hmapK : ∀ x : G, x ∈ R → (MulAut.conj g) x ∈ K' := by
    intro x hx
    have hx' : x ∈ K'.map (MulAut.conj g⁻¹).toMonoidHom := hx
    rw [Subgroup.mem_map] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have h1 : (MulAut.conj g) x = y := by
      change g * x * g⁻¹ = y
      rw [← hyx]
      group
    rwa [h1]
  have huniqR : ∀ u v : ↥R, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u = v := by
    intro u v hu2 hv2 hu1 hv1
    have hu2' : (u : G) * (u : G) = 1 := by simpa using congrArg Subtype.val hu2
    have hv2' : (v : G) * (v : G) = 1 := by simpa using congrArg Subtype.val hv2
    have h1 : (MulAut.conj g) (u : G) * (MulAut.conj g) (u : G) = 1 := by
      rw [← map_mul, hu2', map_one]
    have h2 : (MulAut.conj g) (v : G) * (MulAut.conj g) (v : G) = 1 := by
      rw [← map_mul, hv2', map_one]
    have h3 : (MulAut.conj g) (u : G) ≠ 1 := by
      intro hc
      have h6 : (u : G) = 1 := by
        have h7 : (MulAut.conj g) (u : G) = (MulAut.conj g) (1 : G) := by rw [hc, map_one]
        exact (MulAut.conj g).injective h7
      exact hu1 (Subtype.ext h6)
    have h4 : (MulAut.conj g) (v : G) ≠ 1 := by
      intro hc
      have h6 : (v : G) = 1 := by
        have h7 : (MulAut.conj g) (v : G) = (MulAut.conj g) (1 : G) := by rw [hc, map_one]
        exact (MulAut.conj g).injective h7
      exact hv1 (Subtype.ext h6)
    have h5 := huniqK' ((MulAut.conj g) (u : G)) ((MulAut.conj g) (v : G))
      (hmapK (u : G) u.2) (hmapK (v : G) v.2) h1 h2 h3 h4
    exact Subtype.ext ((MulAut.conj g).injective h5)
  obtain ⟨hQ⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp h.hSuz
  have hexp : ∀ x : ↥R, x ^ 4 = 1 := by
    intro w
    have h1 : (Subgroup.inclusion hRQ w : ↥Q) ^ 4 = 1 :=
      Work.ZassenhausSuzuki.suzuki_pow_four_eq_one (Q := Q) h.hSuz _
    refine Subtype.ext ?_
    simpa using congrArg Subtype.val h1
  have hnoinv : ∀ x y : ↥R, y * x * y⁻¹ = x⁻¹ → x * x = 1 := by
    intro w v hv
    have h1 : (Subgroup.inclusion hRQ v) * (Subgroup.inclusion hRQ w) * (Subgroup.inclusion hRQ v)⁻¹
        = (Subgroup.inclusion hRQ w)⁻¹ := by
      have h2 := congrArg (Subgroup.inclusion hRQ) hv
      simpa using h2
    have h3 := no_inverting_pair_of_suzuki2_q2 h.hSuz h.hord
      (Subgroup.inclusion hRQ w) (Subgroup.inclusion hRQ v) h1
    refine Subtype.ext ?_
    simpa using congrArg Subtype.val h3
  have hcommel : ∀ a b : ↥R,
      Subgroup.inclusion hRQ (a * b * a⁻¹ * b⁻¹)
        = ⁅Subgroup.inclusion hRQ a, Subgroup.inclusion hRQ b⁆ := by
    intro a b
    simp only [commutatorElement_def, map_mul, map_inv]
  have hcsq : ∀ a b : ↥R, (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
    intro a b
    refine Subtype.ext ?_
    have hmem : Subgroup.inclusion hRQ (a * b * a⁻¹ * b⁻¹) ∈ Work.Higman.omega1 ↥Q := by
      rw [hcommel a b, ← Work.Higman.center_eq_omega1_new hQ, ← Work.Higman.commutator_eq_center hQ]
      exact Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) trivial trivial
    have h1 : (Subgroup.inclusion hRQ (a * b * a⁻¹ * b⁻¹)) ^ 2 = 1 :=
      (Work.Higman.IsSuzuki2Grp.mem_omega1 hQ).mp hmem
    simpa [pow_two] using congrArg Subtype.val h1
  have hccent : ∀ a b c : ↥R, c * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * c := by
    intro a b c
    refine Subtype.ext ?_
    have hmem : Subgroup.inclusion hRQ (a * b * a⁻¹ * b⁻¹) ∈ Subgroup.center ↥Q := by
      rw [hcommel a b, ← Work.Higman.commutator_eq_center hQ]
      exact Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) trivial trivial
    have h1 := Subgroup.mem_center_iff.mp hmem (Subgroup.inclusion hRQ c)
    simpa using congrArg Subtype.val h1
  have hle4 : Nat.card ↥R ≤ 4 :=
    card_le_four_of_unique_involution (R := ↥R) hexp huniqR hnoinv hcsq hccent
  have hkAle4 : kA A ≤ 4 := hRcard ▸ hle4
  have hkAge2 : 2 ≤ kA A := by
    have hne : Nat.card ↥K' ≠ 1 := by
      intro hc
      have hbot : K' = ⊥ := (Subgroup.eq_bot_iff_card K').mpr hc
      rw [hbot] at hzmem
      exact hz1 (Subgroup.mem_bot.mp hzmem)
    have hpos : 1 ≤ Nat.card ↥K' := Nat.card_pos
    rw [hK'card] at hne hpos
    omega
  have hpow : ∃ n : ℕ, kA A = 2 ^ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpR : IsPGroup 2 ↥R := h.h2.to_le hRQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpR
    exact ⟨n, by rw [← hRcard, hn]⟩
  obtain ⟨n, hn⟩ := hpow
  rcases n with _ | _ | k
  · simp at hn
    omega
  · left
    norm_num at hn
    exact hn
  · right
    have h4 : 4 ≤ kA A := by
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Work.ZassenhausSuzuki.Odd

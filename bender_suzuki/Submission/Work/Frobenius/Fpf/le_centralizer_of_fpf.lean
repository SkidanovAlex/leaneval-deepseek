import Mathlib
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Fpf centralizer lemma (F7)

If `α` is an automorphism of a finite group `K` with `α ^ q = 1` (`q > 1`) whose nontrivial
powers `α ^ i`, `0 < i < q`, are fixed-point-free, then every `α`-invariant subgroup `Q` whose
order is coprime to the order of an `α`-invariant normal abelian subgroup `V` centralizes `V`.

This is the key input for the solvable case of Thompson theorem on fixed-point-free
automorphisms (`NOTES_LEAD_ft_npc.md`, section 2, lemma F7).
-/

namespace Work.Frobenius.Fpf

set_option linter.style.haveILetI false

open scoped IsMulCommutative
open Work.NPC.Fpf

variable {K : Type*} [Group K]

/-! ### Conjugation by an element of `K` on a normal subgroup -/

/-- Conjugation by `g`, as an automorphism of a normal subgroup `V`. -/
private noncomputable def conjV {V : Subgroup K} (hVn : V.Normal) (g : K) : ↥V ≃* ↥V where
  toFun u := ⟨g * (u : K) * g⁻¹, hVn.conj_mem (u : K) u.2 g⟩
  invFun u := ⟨g⁻¹ * (u : K) * g, by simpa using hVn.conj_mem (u : K) u.2 g⁻¹⟩
  left_inv u := by ext; group
  right_inv u := by ext; group
  map_mul' u v := by ext; simp only [Subgroup.coe_mul]; group

private lemma conjV_apply {V : Subgroup K} (hVn : V.Normal) (g : K) (u : ↥V) :
    ((conjV hVn g u : ↥V) : K) = g * (u : K) * g⁻¹ := rfl

private lemma conjV_one {V : Subgroup K} (hVn : V.Normal) (u : ↥V) : conjV hVn 1 u = u := by
  ext; simp only [conjV_apply, one_mul, inv_one, mul_one]

private lemma conjV_mul {V : Subgroup K} (hVn : V.Normal) (g h : K) (u : ↥V) :
    conjV hVn (g * h) u = conjV hVn g (conjV hVn h u) := by
  ext; simp only [conjV_apply]; group

/-! ### The element `α ^ i u` of an invariant subgroup -/

/-- `α ^ i u`, as an element of an `α`-invariant subgroup. -/
private noncomputable def genPower {α : MulAut K} {V : Subgroup K} (hVα : IsInv α V) (u : ↥V)
    (i : ℕ) : ↥V :=
  ⟨(α ^ i) (u : K), ((hVα.pow i) (u : K)).mpr u.2⟩

private lemma genPower_coe {α : MulAut K} {V : Subgroup K} (hVα : IsInv α V) (u : ↥V) (i : ℕ) :
    ((genPower hVα u i : ↥V) : K) = (α ^ i) (u : K) := rfl

private lemma genPower_zero {α : MulAut K} {V : Subgroup K} (hVα : IsInv α V) (u : ↥V) :
    genPower hVα u 0 = u := by
  ext; simp only [genPower_coe, pow_zero, MulAut.one_apply]

private lemma restrictEquiv_genPower {α : MulAut K} {V : Subgroup K} (hVα : IsInv α V) (u : ↥V)
    (i : ℕ) : hVα.restrictEquiv (genPower hVα u i) = genPower hVα u (i + 1) := by
  ext
  simp only [IsInv.restrictEquiv_apply, genPower_coe, pow_succ', MulAut.mul_apply]

/-! ### The norm `∏ i < q, α ^ i u` -/

/-- The norm `N(u) = ∏ i < q, α ^ i u`, taken inside the abelian group `↥V`. -/
private noncomputable def trNorm {α : MulAut K} {V : Subgroup K} [IsMulCommutative ↥V]
    (hVα : IsInv α V) (q : ℕ) (u : ↥V) : ↥V :=
  ∏ i ∈ Finset.range q, genPower hVα u i

private lemma genPower_self {α : MulAut K} {V : Subgroup K} (hVα : IsInv α V) (u : ↥V) {q : ℕ}
    (hαq : ∀ x : K, (α ^ q) x = x) : genPower hVα u q = genPower hVα u 0 := by
  ext
  simpa only [genPower_coe, pow_zero, MulAut.one_apply] using hαq (u : K)

private lemma prod_range_shift {M : Type*} [CommMonoid M] (f : ℕ → M) {q : ℕ} (hf : f q = f 0) :
    ∏ k ∈ Finset.range q, f (k + 1) = ∏ k ∈ Finset.range q, f k := by
  rcases q with _ | q
  · simp
  · rw [Finset.prod_range_succ (fun k => f (k + 1)) q, Finset.prod_range_succ' f q, hf]

/-- The norm is fixed by `α`. -/
private lemma trNorm_fixed {α : MulAut K} {V : Subgroup K} [IsMulCommutative ↥V]
    (hVα : IsInv α V) {q : ℕ} (hαq : ∀ x : K, (α ^ q) x = x) (u : ↥V) :
    hVα.restrictEquiv (trNorm hVα q u) = trNorm hVα q u := by
  have h1 : hVα.restrictEquiv (trNorm hVα q u)
      = ∏ i ∈ Finset.range q, genPower hVα u (i + 1) := by
    rw [trNorm, map_prod]
    exact Finset.prod_congr rfl (fun i _ => restrictEquiv_genPower hVα u i)
  rw [h1, trNorm]
  exact prod_range_shift _ (genPower_self hVα u hαq)

/-- For a fixed-point-free `α`, the norm of any `u` is `1`. -/
private lemma trNorm_eq_one {α : MulAut K} {V : Subgroup K} [IsMulCommutative ↥V]
    (hVα : IsInv α V) {q : ℕ} (hαq : ∀ x : K, (α ^ q) x = x) (hα : IsFpf α) (u : ↥V) :
    trNorm hVα q u = 1 := by
  have hfix := trNorm_fixed hVα hαq u
  have h2 : IsFpf hVα.restrictEquiv := isFpf_restrict hVα hα
  exact h2 (trNorm hVα q u) hfix

/-! ### The key product identity -/

/-- For `f ∈ Q` and `v ∈ V`, `∏ i < q, c_f (α ^ i (f⁻¹ v f)) = 1`. -/
private lemma key_prod {α : MulAut K} {q : ℕ} {V Q : Subgroup K} [IsMulCommutative ↥V]
    (hVn : V.Normal) (hVα : IsInv α V) (_hQα : IsInv α Q)
    (hαq : ∀ x : K, (α ^ q) x = x) (hα : IsFpf α) (f : ↥Q) (v : ↥V) :
    ∏ i ∈ Finset.range q,
      conjV hVn ((f : K) * ((α ^ i) (f : K))⁻¹) (genPower hVα v i) = 1 := by
  let w : ↥V := ⟨(f : K)⁻¹ * (v : K) * (f : K),
    by simpa using hVn.conj_mem (v : K) v.2 ((f : K)⁻¹)⟩
  have hwval : (w : K) = (f : K)⁻¹ * (v : K) * (f : K) := rfl
  have htr : trNorm hVα q w = 1 := trNorm_eq_one hVα hαq hα w
  have hconj : (∏ i ∈ Finset.range q, conjV hVn (f : K) (genPower hVα w i)) = 1 := by
    have h1 : conjV hVn (f : K) (trNorm hVα q w) = 1 := by rw [htr, map_one]
    rwa [trNorm, map_prod] at h1
  have hterm : ∀ i, conjV hVn (f : K) (genPower hVα w i) =
      conjV hVn ((f : K) * ((α ^ i) (f : K))⁻¹) (genPower hVα v i) := by
    intro i
    ext
    simp only [conjV_apply, genPower_coe, hwval, map_mul, map_inv]
    group
  rw [← hconj]
  exact Finset.prod_congr rfl (fun i _ => (hterm i).symm)

/-! ### The centralizer of `Q` inside `V` -/

/-- The subgroup of `↥V` of elements centralizing `Q`. -/
private noncomputable def centSub (Q V : Subgroup K) : Subgroup ↥V :=
  (Subgroup.centralizer (Q : Set K)).comap (Subgroup.subtype V)

private lemma mem_centSub_iff {V Q : Subgroup K} {u : ↥V} :
    u ∈ centSub Q V ↔ ∀ g : K, g ∈ Q → g * (u : K) = (u : K) * g := by
  rw [centSub, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  simp only [SetLike.mem_coe, Subgroup.coe_subtype]

private lemma mem_centSub_iff_conj {V Q : Subgroup K} (hVn : V.Normal) {u : ↥V} :
    u ∈ centSub Q V ↔ ∀ g : K, g ∈ Q → conjV hVn g u = u := by
  rw [mem_centSub_iff]
  constructor
  · intro h g hg
    ext
    rw [conjV_apply, h g hg]
    group
  · intro h g hg
    have h2 := congrArg (fun x : ↥V => (x : K)) (h g hg)
    rw [conjV_apply] at h2
    calc g * (u : K) = (g * (u : K) * g⁻¹) * g := by group
      _ = (u : K) * g := by rw [h2]

/-! ### The map `f ↦ f * (α ^ i f)⁻¹` on `Q` -/

private noncomputable def phiQ {α : MulAut K} {Q : Subgroup K} (hQα : IsInv α Q) (i : ℕ)
    (f : ↥Q) : ↥Q :=
  ⟨(f : K) * ((α ^ i) (f : K))⁻¹, Q.mul_mem f.2 (Q.inv_mem (((hQα.pow i) (f : K)).mpr f.2))⟩

private lemma phiQ_coe {α : MulAut K} {Q : Subgroup K} (hQα : IsInv α Q) (i : ℕ) (f : ↥Q) :
    ((phiQ hQα i f : ↥Q) : K) = (f : K) * ((α ^ i) (f : K))⁻¹ := rfl

private lemma phiQ_zero {α : MulAut K} {Q : Subgroup K} (hQα : IsInv α Q) (f : ↥Q) :
    phiQ hQα 0 f = 1 := by
  ext
  simp only [phiQ_coe, pow_zero, MulAut.one_apply, Subgroup.coe_one, mul_inv_cancel]

/-- For `0 < i < q`, the map `f ↦ f (α ^ i f)⁻¹` is injective on `Q`. -/
private lemma phiQ_injective {α : MulAut K} {q : ℕ} {Q : Subgroup K} (hQα : IsInv α Q)
    (hpow : ∀ i : ℕ, 0 < i → i < q → IsFpf (α ^ i)) {i : ℕ} (hi0 : 0 < i) (hiq : i < q) :
    Function.Injective (phiQ hQα i) := by
  intro f₁ f₂ h
  have h' : (f₁ : K) * ((α ^ i) (f₁ : K))⁻¹ = (f₂ : K) * ((α ^ i) (f₂ : K))⁻¹ := by
    have := congrArg (fun f : ↥Q => (f : K)) h
    simpa only [phiQ_coe] using this
  have h2 : ((f₂ : K)⁻¹ * (f₁ : K)) = (α ^ i) ((f₂ : K)⁻¹ * (f₁ : K)) := by
    calc (f₂ : K)⁻¹ * (f₁ : K)
        = (f₂ : K)⁻¹ * ((f₁ : K) * ((α ^ i) (f₁ : K))⁻¹) * ((α ^ i) (f₁ : K)) := by group
      _ = (f₂ : K)⁻¹ * ((f₂ : K) * ((α ^ i) (f₂ : K))⁻¹) * ((α ^ i) (f₁ : K)) := by rw [h']
      _ = (α ^ i) ((f₂ : K)⁻¹ * (f₁ : K)) := by rw [map_mul, map_inv]; group
  have h3 : (f₂ : K)⁻¹ * (f₁ : K) = 1 := (hpow i hi0 hiq) _ h2.symm
  exact Subtype.ext (inv_mul_eq_one.mp h3).symm

/-! ### The element `σ(u) = ∏ g ∈ Q, c_g(u)` -/

private noncomputable def sigma {V : Subgroup K} [IsMulCommutative ↥V] (Q : Subgroup K)
    [Fintype ↥Q] (hVn : V.Normal) (u : ↥V) : ↥V :=
  ∏ g : ↥Q, conjV hVn (g : K) u

/-- `σ(u)` is centralized by `Q`. -/
private lemma sigma_mem {V Q : Subgroup K} [IsMulCommutative ↥V] [Fintype ↥Q]
    (hVn : V.Normal) (u : ↥V) : sigma Q hVn u ∈ centSub Q V := by
  have hm : sigma Q hVn u ∈ centSub Q V ↔
      ∀ g : K, g ∈ Q → conjV hVn g (sigma Q hVn u) = sigma Q hVn u :=
    mem_centSub_iff_conj (V := V) (Q := Q) (u := sigma Q hVn u) hVn
  rw [hm]
  intro g hg
  have key : ∀ f : ↥Q, conjV hVn g (conjV hVn (f : K) u) =
      conjV hVn ((⟨g, hg⟩ * f : ↥Q) : K) u := by
    intro f
    simp only [← conjV_mul, Subgroup.coe_mul]
  rw [sigma, map_prod]
  show (∏ f : ↥Q, conjV hVn g (conjV hVn (f : K) u)) = ∏ f : ↥Q, conjV hVn (f : K) u
  calc ∏ f : ↥Q, conjV hVn g (conjV hVn (f : K) u)
      = ∏ f : ↥Q, conjV hVn ((⟨g, hg⟩ * f : ↥Q) : K) u :=
        Finset.prod_congr rfl (fun f _ => key f)
    _ = ∏ f : ↥Q, conjV hVn (f : K) u := by
        rw [← Equiv.prod_comp (Equiv.mulLeft (⟨g, hg⟩ : ↥Q)) (fun f : ↥Q => conjV hVn (f : K) u)]
        exact Finset.prod_congr rfl (fun f _ => rfl)

/-! ### Coprimality -/

/-- If `|Q|` is coprime to `|V|` and `u ^ |Q|` lies in a subgroup `C ≤ ↥V`, then so does `u`:
`u` is a power of `u ^ |Q|` because `|Q|` is coprime to the order of `u`. -/
private lemma mem_of_pow_mem {V Q : Subgroup K} [IsMulCommutative ↥V] [Fintype ↥Q]
    [Fintype ↥V] {C : Subgroup ↥V} {u : ↥V}
    (hcop : (Nat.card ↥Q).Coprime (Nat.card ↥V))
    (hu : u ^ Fintype.card ↥Q ∈ C) : u ∈ C := by
  have hcard : Fintype.card ↥Q = Nat.card ↥Q := Nat.card_eq_fintype_card.symm
  rw [hcard] at hu
  have hdvd : orderOf u ∣ Nat.card ↥V := orderOf_dvd_natCard u
  have hcop2 : (Nat.card ↥Q).Coprime (orderOf u) :=
    Nat.Coprime.coprime_dvd_right hdvd hcop
  haveI : Nonempty ↥V := ⟨1⟩
  have hpos : 0 < Nat.card ↥V := Nat.card_pos
  have hdpos : 0 < orderOf u := Nat.pos_of_dvd_of_pos hdvd hpos
  have hphi : 0 < Nat.totient (orderOf u) := Nat.totient_pos.mpr hdpos
  have hmod : (Nat.card ↥Q) ^ (Nat.totient (orderOf u)) ≡ 1 [MOD orderOf u] :=
    Nat.ModEq.pow_totient hcop2
  have hpow : u ^ ((Nat.card ↥Q) ^ Nat.totient (orderOf u)) = u := by
    rw [pow_eq_pow_of_modEq hmod (pow_orderOf_eq_one u), pow_one]
  have hmul : (Nat.card ↥Q) * (Nat.card ↥Q) ^ (Nat.totient (orderOf u) - 1)
      = (Nat.card ↥Q) ^ Nat.totient (orderOf u) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt hphi)]
  have hkey : u = (u ^ Nat.card ↥Q) ^ ((Nat.card ↥Q) ^ (Nat.totient (orderOf u) - 1)) := by
    rw [← pow_mul, hmul, hpow]
  rw [hkey]
  exact Subgroup.pow_mem C hu _

/-! ### The main computation -/

/-- Every `v ∈ V` centralizes `Q`. -/
private lemma key_central {α : MulAut K} {q : ℕ} {V Q : Subgroup K}
    [IsMulCommutative ↥V] [Fintype ↥Q] [Fintype ↥V]
    (hVn : V.Normal) (hVα : IsInv α V) (hQα : IsInv α Q)
    (hq : 1 < q) (hαq : ∀ x : K, (α ^ q) x = x)
    (hpow : ∀ i : ℕ, 0 < i → i < q → IsFpf (α ^ i))
    (hcop : (Nat.card ↥Q).Coprime (Nat.card ↥V)) (v : ↥V) : v ∈ centSub Q V := by
  have hα : IsFpf α := by
    have h := hpow 1 (by norm_num) hq
    simpa using h
  have hprod : (∏ f : ↥Q, ∏ i ∈ Finset.range q,
      conjV hVn (phiQ hQα i f : K) (genPower hVα v i)) = 1 :=
    Finset.prod_eq_one (fun f _ => key_prod hVn hVα hQα hαq hα f v)
  have hsplit : (∏ f : ↥Q, ∏ i ∈ Finset.range q,
        conjV hVn (phiQ hQα i f : K) (genPower hVα v i))
      = (∏ f : ↥Q, (∏ i ∈ Finset.range (q - 1),
          conjV hVn (phiQ hQα (i + 1) f : K) (genPower hVα v (i + 1))) * v) := by
    apply Finset.prod_congr rfl
    intro f _
    have hq1 : q - 1 + 1 = q := by omega
    have h0 : conjV hVn (phiQ hQα 0 f : K) (genPower hVα v 0) = v := by
      have h1 : ((phiQ hQα 0 f : ↥Q) : K) = 1 := by rw [phiQ_zero]; rfl
      rw [h1, conjV_one, genPower_zero]
    rw [show Finset.range q = Finset.range (q - 1 + 1) from by rw [hq1],
      Finset.prod_range_succ', h0]
  have hdist : (∏ f : ↥Q, (∏ i ∈ Finset.range (q - 1),
        conjV hVn (phiQ hQα (i + 1) f : K) (genPower hVα v (i + 1))) * v)
      = (∏ f : ↥Q, ∏ i ∈ Finset.range (q - 1),
          conjV hVn (phiQ hQα (i + 1) f : K) (genPower hVα v (i + 1)))
        * v ^ Fintype.card ↥Q := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hswap : (∏ f : ↥Q, ∏ i ∈ Finset.range (q - 1),
        conjV hVn (phiQ hQα (i + 1) f : K) (genPower hVα v (i + 1)))
      = (∏ i ∈ Finset.range (q - 1), ∏ f : ↥Q,
          conjV hVn (phiQ hQα (i + 1) f : K) (genPower hVα v (i + 1))) :=
    Finset.prod_comm
  have hreindex : (∏ i ∈ Finset.range (q - 1), ∏ f : ↥Q,
        conjV hVn (phiQ hQα (i + 1) f : K) (genPower hVα v (i + 1)))
      = (∏ i ∈ Finset.range (q - 1), sigma Q hVn (genPower hVα v (i + 1))) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiq : i + 1 < q := by
      have := Finset.mem_range.mp hi
      omega
    have hbij : Function.Bijective (phiQ hQα (i + 1)) :=
      (Finite.injective_iff_bijective).mp (phiQ_injective hQα hpow (by omega) hiq)
    simp only [sigma]
    rw [← Equiv.prod_comp (Equiv.ofBijective (phiQ hQα (i + 1)) hbij)
      (fun f : ↥Q => conjV hVn (f : K) (genPower hVα v (i + 1)))]
    exact Finset.prod_congr rfl (fun f _ => by rw [Equiv.ofBijective_apply])
  have hmain : (∏ i ∈ Finset.range (q - 1), sigma Q hVn (genPower hVα v (i + 1)))
      * v ^ Fintype.card ↥Q = 1 := by
    rw [← hreindex, ← hswap, ← hdist, ← hsplit, hprod]
  have hA : (∏ i ∈ Finset.range (q - 1), sigma Q hVn (genPower hVα v (i + 1)))
      ∈ centSub Q V :=
    Subgroup.prod_mem _ (fun i _ => sigma_mem hVn _)
  have hvpow : v ^ Fintype.card ↥Q ∈ centSub Q V := by
    have h1 : v ^ Fintype.card ↥Q =
        (∏ i ∈ Finset.range (q - 1), sigma Q hVn (genPower hVα v (i + 1)))⁻¹ :=
      (inv_eq_of_mul_eq_one_right hmain).symm
    rw [h1]
    exact Subgroup.inv_mem _ hA
  exact mem_of_pow_mem hcop hvpow

/-! ### The main theorem -/

theorem le_centralizer_of_fpf {K : Type*} [Group K] [Finite K] {α : MulAut K} {q : ℕ}
    (hq : 1 < q) (hαq : ∀ x : K, (α ^ q) x = x)
    (hpow : ∀ i : ℕ, 0 < i → i < q → Work.NPC.Fpf.IsFpf (α ^ i))
    {V Q : Subgroup K} (hVn : V.Normal) (hVab : IsMulCommutative ↥V)
    (hVα : Work.NPC.Fpf.IsInv α V) (hQα : Work.NPC.Fpf.IsInv α Q)
    (hcop : (Nat.card Q).Coprime (Nat.card V)) :
    Q ≤ Subgroup.centralizer (V : Set K) := by
  haveI := hVab
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
  intro f hf
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv1 : (⟨v, hv⟩ : ↥V) ∈ centSub Q V :=
    key_central hVn hVα hQα hq hαq hpow hcop ⟨v, hv⟩
  rw [mem_centSub_iff] at hv1
  exact (hv1 f hf).symm

end Work.Frobenius.Fpf

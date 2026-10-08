import Mathlib
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.pow_four_of_mulEquiv
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.qPt_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary lemmas for `szTilde_sq` (BG 5.13 / 5.14)

Vocabulary: the reflection map `∼` of `SzTildeDefs` in terms of the canonical structure maps,
the structure equation, and the subgroup `E = ⟨μ a⟩` machinery.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Helper: `g * (x * g) * g⁻¹ = g * x`. -/
theorem mul_mul_mul_inv_cancel (g x : G) : g * (x * g) * g⁻¹ = g * x := by group

/-- Helper: `g * (x * g⁻¹) * g⁻¹ = g * x * g⁻²`. -/
theorem inv_conj_eq (g x : G) : (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ := by group

/-- Helper: `g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹`. -/
theorem inv_conj_eq' (g x : G) : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := (inv_conj_eq g x).symm

/-- The `h`-coordinate of a canonical structure, as an element of `G` (it lies in
`D = twoPoint H t`). -/
abbrev hG (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) : G :=
  ((C.h x : ↥(twoPoint H t)) : G)

/-- The `f`-coordinate of a canonical structure, as an element of `G`. -/
abbrev fG (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) : G := ((C.f x : Q) : G)

/-- The `g`-coordinate of a canonical structure, as an element of `G`. -/
abbrev gG (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) : G := ((C.g x : Q) : G)

/-- **The reflection map** `∼ x = g (g x)⁻¹` attached to a canonical structure (this is
`szTilde`, whose definition unfolds to `tildeOf (szCanon hsplit)`). -/
noncomputable def tildeOf (C : Work.ZassenhausPSL2.Canon H Q t) : Q → Q :=
  fun x => if (x : G) = 1 then 1 else C.g ((C.g x)⁻¹)

theorem szTilde_eq_tildeOf (hsplit : IsSplitRankOne H Q t) :
    szTilde hsplit = tildeOf (szCanon hsplit) := rfl

/-- The `Q`-part `g x` of the canonical form of `t x t` is non-trivial for `x ≠ 1`. -/
theorem canon_g_ne_one (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q}
    (hx : (x : G) ≠ 1) : (C.g x : G) ≠ 1 := by
  intro hg
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  have hspec := C.spec x hx
  simp only [hg, one_mul] at hspec
  have hx' : (x : G) = (hG C x)⁻¹ * fG C x * t := by
    calc (x : G) = t * (t * (x : G) * t) * t := by
          have h := Work.RankOneUniqueness.involution_conj (e := (x : G)) ht2
          rw [Work.RankOneUniqueness.inv_eq_self hsplit] at h
          exact h.symm
      _ = t * (hG C x * t * fG C x) * t := by rw [hspec]
      _ = (hG C x)⁻¹ * fG C x * t := by
          rw [← canon_t_conj_inv_D hsplit hzass h2 (C.h x).2]
          group
  have ht_mem : t ∈ H := by
    have h1 : (fG C x)⁻¹ * (hG C x) * (x : G) = t := by
      rw [hx']
      group
    rw [← h1]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hsplit.le (C.f x).2)) ((C.h x).2).1)
      (hsplit.le x.2)
  exact hsplit.not_mem ht_mem

/-- `h x · t · h x = t`. -/
theorem canon_h_t_h (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) :
    hG C x * t * hG C x = t := by
  have h := canon_t_conj_inv_D hsplit hzass h2 (C.h x).2
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  calc hG C x * t * hG C x = hG C x * t * hG C x * (t * t) := by rw [ht2, mul_one]
    _ = hG C x * (t * hG C x * t) * t := by group
    _ = hG C x * (hG C x)⁻¹ * t := by rw [h]
    _ = t := by group

/-- `t · h x` is an involution. -/
theorem t_mul_h_sq (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) :
    (t * hG C x) * (t * hG C x) = 1 := by
  have h := canon_h_t_h hsplit hzass h2 C x
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  calc (t * hG C x) * (t * hG C x) = t * (hG C x * t * hG C x) := by group
    _ = t * t := by rw [h]
    _ = 1 := ht2

/-- `t * (h x)⁻¹ = h x * t`. -/
theorem t_mul_hinv (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) (x : Q) :
    t * (hG C x)⁻¹ = hG C x * t := by
  have h := canon_t_conj_inv_D hsplit hzass h2 (C.h x).2
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  calc t * (hG C x)⁻¹ = t * (t * hG C x * t) := by rw [h]
    _ = (t * t) * hG C x * t := by group
    _ = hG C x * t := by rw [ht2, one_mul]

/-- **BG 3.1 (j)**: the reflection map in terms of the canonical structure maps:
`∼ x = (h x)⁻¹ · f(x) · h x` for `x ≠ 1`. -/
theorem tildeOf_eq (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    ((tildeOf C x : Q) : G) = (hG C x)⁻¹ * fG C x * hG C x := by
  have htilde : (tildeOf C x : Q) = C.g ((C.g x)⁻¹) := by
    rw [tildeOf]
    simp only [hx, ite_false]
  have hgne : ((((C.g x)⁻¹ : Q)) : G) ≠ 1 := by
    simpa using canon_g_ne_one hsplit hzass h2 C hx
  have hH1 := canon_H1 hsplit C ((C.g x)⁻¹) hgne
  have hH1' : C.g ((C.g x)⁻¹) = (C.f (C.g x))⁻¹ := by
    have h := congrArg Inv.inv hH1
    simpa using h
  have hH4 := canon_H4 hsplit hzass h2 C x hx
  calc ((tildeOf C x : Q) : G) = ((C.g ((C.g x)⁻¹) : Q) : G) := by rw [htilde]
    _ = (((C.f (C.g x))⁻¹ : Q) : G) := by rw [hH1']
    _ = (fG C (C.g x))⁻¹ := by simp
    _ = (hG C x)⁻¹ * fG C x * hG C x := by
        rw [show fG C (C.g x) = (hG C x)⁻¹ * (fG C x)⁻¹ * hG C x from hH4]
        group

/-- **BG 3.3 (a)**, the structure equation of the reflection: for an involution `x ∈ Q#`,
`(∼ x)⁻¹ · (t h_x) · (∼ x) = (t h_x)⁻¹ · x · (t h_x)`. -/
theorem tildeOf_conj_mu (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q}
    (hx : (x : G) ≠ 1) (hinv : x * x = 1) :
    (((tildeOf C x : Q) : G))⁻¹ * (t * hG C x) * ((tildeOf C x : Q) : G)
      = (t * hG C x)⁻¹ * (x : G) * (t * hG C x) := by
  have hinv' : x⁻¹ = x := inv_eq_of_mul_eq_one_left hinv
  have hg : gG C x = (fG C x)⁻¹ := by
    have h1 := canon_H1 hsplit C x hx
    have h1' : ((C.g x)⁻¹ : Q) = C.f x := by simpa [hinv'] using h1
    have h3 : (gG C x)⁻¹ = fG C x := by
      simpa using congrArg (fun y : Q => (y : G)) h1'
    rw [← h3, inv_inv]
  have hspec := C.spec x hx
  have htinv : t⁻¹ = t := canon_t_inv hsplit
  have hft : (fG C x)⁻¹ * hG C x * t * fG C x = t * (x : G) * t := by
    rw [← hg, hspec]
  rw [tildeOf_eq hsplit hzass h2 C hx]
  have hstep : ((hG C x)⁻¹ * fG C x * hG C x)⁻¹ * (t * hG C x) * ((hG C x)⁻¹ * fG C x * hG C x)
      = (hG C x)⁻¹ * ((fG C x)⁻¹ * hG C x * t * fG C x) * hG C x := by group
  rw [hstep, hft]
  rw [mul_inv_rev, htinv]
  group

/-- The reflection of `szTilde` in terms of the canonical structure maps. -/
theorem szTilde_eq (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {x : Q} (hx : (x : G) ≠ 1) :
    ((szTilde hsplit x : Q) : G)
      = (hG (szCanon hsplit) x)⁻¹ * fG (szCanon hsplit) x * hG (szCanon hsplit) x := by
  rw [szTilde_eq_tildeOf]
  exact tildeOf_eq hsplit hzass h2 (szCanon hsplit) hx

/-- The structure equation for `szTilde` (BG 3.3 (a)). -/
theorem szTilde_conj_mu (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) {x : Q} (hx : (x : G) ≠ 1) (hinv : x * x = 1) :
    (((szTilde hsplit x : Q) : G))⁻¹ * (t * hG (szCanon hsplit) x) * ((szTilde hsplit x : Q) : G)
      = (t * hG (szCanon hsplit) x)⁻¹ * (x : G) * (t * hG (szCanon hsplit) x) := by
  rw [szTilde_eq_tildeOf]
  exact tildeOf_conj_mu hsplit hzass h2 (szCanon hsplit) hx hinv

/-! ## The central involutions of `Q` in coordinates -/

section Coords

variable {K : Type*} [Field K] {θ : K ≃+* K}

/-- The element of `Q` with `e`-coordinates `(0,b)`: the central element of `A(K,θ)`. -/
noncomputable def zc (e : Q ≃* SzA K θ) (b : K) : Q := e.symm ⟨0, b⟩

@[simp] theorem zc_coe (e : Q ≃* SzA K θ) (b : K) :
    e (zc e b) = (⟨0, b⟩ : SzA K θ) := by
  simp [zc]

theorem zc_zero (e : Q ≃* SzA K θ) : zc e 0 = 1 := by
  apply e.injective
  rw [zc_coe, map_one]
  exact rfl

theorem zc_ne_one_iff (e : Q ≃* SzA K θ) {b : K} : zc e b ≠ 1 ↔ b ≠ 0 := by
  constructor
  · intro h hb
    exact h (by rw [hb, zc_zero])
  · intro hb h
    apply hb
    have h' := congrArg (fun y : Q => e y) h
    rw [zc_coe, map_one] at h'
    exact congrArg SzA.b h'

theorem zc_mul_self (e : Q ≃* SzA K θ) [CharP K 2] (b : K) : zc e b * zc e b = 1 := by
  apply e.injective
  simp only [map_mul, map_one, zc_coe]
  ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]

theorem zc_mem_center (e : Q ≃* SzA K θ) (b : K) : zc e b ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  simp only [map_mul, zc_coe]
  ext <;> simp [SzA.mul_a, SzA.mul_b, add_comm, add_left_comm]

theorem zc_injective (e : Q ≃* SzA K θ) : Function.Injective (zc e) := by
  intro b c h
  have h' := congrArg (fun y : Q => e y) h
  simpa [zc] using h'

theorem mem_center_map (e : Q ≃* SzA K θ) {c : Q} (hc : c ∈ Subgroup.center Q) :
    e c ∈ Subgroup.center (SzA K θ) := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← map_mul, hc x, map_mul]

/-- Every central element of `Q` is `zc e b` for some `b` (using `θ ≠ 1`). -/
theorem exists_eq_zc_of_mem_center (e : Q ≃* SzA K θ) (hθ1 : θ ≠ 1) {c : Q}
    (hc : c ∈ Subgroup.center Q) : ∃ b : K, c = zc e b := by
  have hc' : e c ∈ Subgroup.center (SzA K θ) := mem_center_map e hc
  have ha : (e c).a = 0 := (SzA.mem_center_iff θ hθ1 (e c)).mp hc'
  refine ⟨(e c).b, ?_⟩
  apply e.injective
  rw [zc_coe]
  ext <;> simp [ha]

end Coords



/-! ## Zassenhaus and torus facts about the involutions of the root group -/

section Invol

variable {K : Type*} [Field K] [CharP K 2] {θ : K ≃+* K}

/-- The image of the centre of `Q` is the centre of `A(K,θ)` (and conversely). -/
theorem mem_center_iff_map (e : Q ≃* SzA K θ) {c : Q} :
    c ∈ Subgroup.center Q ↔ e c ∈ Subgroup.center (SzA K θ) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, h x, map_mul]
  · intro h y
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e y)

/-- Every involution of `Q` is central: in the coordinates `e` it is `⟨0,b⟩`. -/
theorem involution_mem_center (e : Q ≃* SzA K θ) {s : Q} (hs : s * s = 1) :
    s ∈ Subgroup.center Q := by
  rw [mem_center_iff_map e]
  have hsq : (e s) * (e s) = 1 := by rw [← map_mul, hs, map_one]
  have h2 : (e s) * (e s) = (⟨0, (e s).a * θ (e s).a⟩ : SzA K θ) := SzA.sq_eq θ (e s)
  rw [h2] at hsq
  have ha : (e s).a * θ (e s).a = 0 := by
    simpa using congrArg SzA.b hsq
  have ha0 : (e s).a = 0 := by
    rcases mul_eq_zero.mp ha with h | h
    · exact h
    · exact θ.injective (by rw [h, map_zero])
  rw [show e s = (⟨0, (e s).b⟩ : SzA K θ) from SzA.ext ha0 rfl]
  exact SzA.mk_zero_mem_center θ _

end Invol


/-! ## `Q#` acts freely on `Ω ∖ {∞}` -/

/-- A nontrivial element of `Q` fixes no point of `Ω = G ⧸ H` other than `∞ = H`. -/
theorem fix_eq_pt_of_mem_Q (hsplit : IsSplitRankOne H Q t) {s : Q} (hs : (s : G) ≠ 1)
    {ω : G ⧸ H} (hω : (s : G) • ω = ω) : ω = Work.RankOneUniqueness.pt H := by
  by_contra hne
  obtain ⟨y, hyQ, hyω⟩ := Work.RankOneUniqueness.qPt_surjective hsplit hne
  have h1 : (s : G) • Work.RankOneUniqueness.qPt H t y
      = Work.RankOneUniqueness.qPt H t ((s : G) * y) := by
    show (((s : G) * ((y : G) * t) : G) : G ⧸ H) = ((((s : G) * y) * t : G) : G ⧸ H)
    rw [mul_assoc]
  have h2 : Work.RankOneUniqueness.qPt H t ((s : G) * y) = Work.RankOneUniqueness.qPt H t y := by
    rw [← h1, hyω, hω]
  have hsy : (s : G) * y = y :=
    Work.RankOneUniqueness.qPt_injective hsplit (Q.mul_mem s.2 hyQ) hyQ h2
  have hs1 : s = 1 := by
    apply Subtype.ext
    have := congrArg (fun z : G => z * y⁻¹) hsy
    simpa using this
  exact hs (by simpa using congrArg (fun z : Q => (z : G)) hs1)

/-- An element of `G` commuting with a nontrivial element of `Q` lies in `H`. -/
theorem commute_mem_H_of_mem_Q (hsplit : IsSplitRankOne H Q t) {s : Q} (hs : (s : G) ≠ 1)
    {x : G} (hcomm : (s : G) * x = x * (s : G)) : x ∈ H := by
  have hsH : (s : G) ∈ H := hsplit.le s.2
  have hfix : x • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H := by
    refine fix_eq_pt_of_mem_Q hsplit hs ?_
    calc (s : G) • (x • Work.RankOneUniqueness.pt H)
        = ((s : G) * x) • Work.RankOneUniqueness.pt H := by rw [mul_smul]
      _ = (x * (s : G)) • Work.RankOneUniqueness.pt H := by rw [hcomm]
      _ = x • ((s : G) • Work.RankOneUniqueness.pt H) := by rw [mul_smul]
      _ = x • Work.RankOneUniqueness.pt H :=
          congrArg (fun z => x • z) (Work.RankOneUniqueness.smul_pt_of_mem H hsH)
  rwa [Work.RankOneUniqueness.smul_pt_iff] at hfix


/-! ## The torus acts faithfully on the central involutions -/

/-- **The action of `D` on the central involutions of `Q` is faithful.**  If `d ∈ D` fixes the
non-trivial central element `s ∈ Z(Q)` then `d = 1`: the parameter `λ(d)` satisfies
`λ · θλ = 1`, hence `λ = 1` (`Odd (orderOf θ)`), hence `d` acts trivially on `Q` and therefore
fixes the three points `∞`, `qPt 1`, `qPt x₀` of `Ω = G ⧸ H`. -/
theorem eq_one_of_mem_twoPoint_of_conj_central {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {d : G} (hd : d ∈ twoPoint H t) {s : Q} (hscen : s ∈ Subgroup.center Q)
    (hs1 : (s : G) ≠ 1) (hconj : d * (s : G) * d⁻¹ = (s : G)) :
    d = 1 := by
  classical
  have hsa : (e s).a = 0 :=
    (SzA.mem_center_iff θ hθ1 (e s)).mp ((mem_center_iff_map e).mp hscen)
  have hes : e s = (⟨0, (e s).b⟩ : SzA (GaloisField 2 m) θ) := SzA.ext hsa rfl
  have hb : (e s).b ≠ 0 := by
    intro hb0
    refine hs1 ?_
    have h : e s = 1 := by rw [hes, hb0]; rfl
    have h' := congrArg (fun z : SzA (GaloisField 2 m) θ => e.symm z) h
    simpa using h'
  obtain ⟨lam, hlam⟩ := htorus d hd
  obtain ⟨y, hy, hye⟩ := hlam s
  have hy_s : y = s := by
    apply Subtype.ext
    rw [hy, hconj]
  have hkey : (lam : GaloisField 2 m) * θ (lam : GaloisField 2 m) = 1 := by
    have heq : e s = SzA.hLam θ (lam : GaloisField 2 m) (e s) := by
      rw [← hye, hy_s]
    rw [hes] at heq
    have h := congrArg SzA.b heq
    simp only [SzA.hLam_b] at h
    exact mul_right_cancel₀ hb (by rw [one_mul, ← h])
  have hlam1 : (lam : GaloisField 2 m) = 1 :=
    eq_one_of_mul_map_eq_one θ hθodd (Units.ne_zero lam) hkey
  have hlamu : lam = 1 := Units.ext hlam1
  have hact : ∀ x : Q, d * (x : G) * d⁻¹ = (x : G) := by
    intro x
    obtain ⟨y, hy, hye⟩ := hlam x
    have hyx : y = x := by
      apply e.injective
      rw [hye, hlamu]
      simpa using SzA.hLam_one θ (e x)
    rw [← hy, hyx]
  have hqpt : ∀ x : Q, d • Work.RankOneUniqueness.qPt H t (x : G)
      = Work.RankOneUniqueness.qPt H t (x : G) := by
    intro x
    have hstep : d • Work.RankOneUniqueness.qPt H t (x : G)
        = Work.RankOneUniqueness.qPt H t (d * (x : G) * d⁻¹) := by
      rw [Work.RankOneUniqueness.qPt, Work.RankOneUniqueness.qPt, Work.RankOneUniqueness.smul_mk]
      refine QuotientGroup.eq.mpr ?_
      have hco : (d * ((x : G) * t))⁻¹ * ((d * (x : G) * d⁻¹) * t) = d := by
        rw [mul_inv_rev, mul_inv_rev, canon_t_inv hsplit]
        rw [show t * (x : G)⁻¹ * d⁻¹ * (d * (x : G) * d⁻¹ * t) = t * d⁻¹ * t from by group]
        exact canon_t_conj_invD_inv hsplit hzass h2 hd
      rw [hco]
      exact Work.RankOneUniqueness.twoPoint_le_left H t hd
    rw [hstep, hact x]
  have hpt : d • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.smul_pt_of_mem H (Work.RankOneUniqueness.twoPoint_le_left H t hd)
  set x₀ : Q := e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) with hx₀
  have hx₀ne : x₀ ≠ 1 := by
    intro h
    have h' := congrArg (fun z : Q => e z) h
    simp only [map_one] at h'
    rw [hx₀, MulEquiv.apply_symm_apply] at h'
    exact one_ne_zero (α := GaloisField 2 m) (by simpa using congrArg SzA.a h')
  have hp₁ : Work.RankOneUniqueness.qPt H t (x₀ : G) ≠ Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.qPt_ne_pt hsplit x₀.2
  have hp₂ : Work.RankOneUniqueness.qPt H t ((1 : Q) : G) ≠ Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.qPt_ne_pt hsplit (1 : Q).2
  have hp₃ : Work.RankOneUniqueness.qPt H t (x₀ : G)
      ≠ Work.RankOneUniqueness.qPt H t ((1 : Q) : G) := by
    intro h
    have h' := Work.RankOneUniqueness.qPt_injective hsplit x₀.2 (1 : Q).2 h
    exact hx₀ne (by simpa using h')
  exact hzass _ _ _ hp₂.symm hp₁.symm hp₃.symm d hpt (hqpt 1) (hqpt x₀)


/-- **`C_H(s) = Q` for an involution `s ∈ Q#`**: an element of `H` centralising `s` lies in `Q`. -/
theorem mem_H_centralizer_involution_le_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {s : Q} (hs1 : (s : G) ≠ 1) (hs2 : s * s = 1)
    {x : G} (hxH : x ∈ H) (hcomm : (s : G) * x = x * (s : G)) : x ∈ Q := by
  have hscen : s ∈ Subgroup.center Q := involution_mem_center e hs2
  obtain ⟨d, q, hdq⟩ := Work.ZassenhausPSL2.mem_eq_dStab_mul_Q hsplit (⟨x, hxH⟩ : H)
  have hdq' : (d : G) * (q : G) = x := by simpa using hdq
  have hsq : (q : G) * (s : G) * (q : G)⁻¹ = (s : G) := by
    have h := (Subgroup.mem_center_iff.mp hscen) q
    have h' : (q : G) * (s : G) = (s : G) * (q : G) := congrArg (fun z : Q => (z : G)) h
    calc (q : G) * (s : G) * (q : G)⁻¹ = (s : G) * (q : G) * (q : G)⁻¹ := by rw [h']
      _ = (s : G) := by group
  have hxsx : x * (s : G) * x⁻¹ = (s : G) := by
    rw [← hcomm]; group
  have hdconj : (d : G) * (s : G) * (d : G)⁻¹ = (s : G) := by
    calc (d : G) * (s : G) * (d : G)⁻¹
        = (d : G) * ((q : G) * (s : G) * (q : G)⁻¹) * (d : G)⁻¹ := by rw [hsq]
      _ = ((d : G) * (q : G)) * (s : G) * ((d : G) * (q : G))⁻¹ := by group
      _ = x * (s : G) * x⁻¹ := by rw [hdq']
      _ = (s : G) := hxsx
  have hd1 : (d : G) = 1 :=
    eq_one_of_mem_twoPoint_of_conj_central hsplit hzass h2 hθ1 hθodd htorus d.2 hscen hs1 hdconj
  rw [hd1, one_mul] at hdq'
  rw [← hdq']
  exact q.2

/-- **`⟨μ a⟩ ∩ Q = 1`** for `a ∈ Z(Q)` a non-trivial involution, `μ = t · h a`. -/
theorem zpowers_mu_mul_a_inf_Q_eq_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q}
    (ha1 : (a : G) ≠ 1) (ha2 : a * a = 1) (hacen : a ∈ Subgroup.center Q) :
    Subgroup.zpowers (t * hG C a * (a : G)) ⊓ Q = ⊥ := by
  set μ : G := t * hG C a with hμ
  set x0 : G := μ * (a : G) with hx0
  have haa : (a : G) * (a : G) = 1 := by simpa using congrArg (fun z : Q => (z : G)) ha2
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  refine le_antisymm ?_ bot_le
  intro e he
  obtain ⟨heE, heQ⟩ := Subgroup.mem_inf.mp he
  rw [Subgroup.mem_bot]
  by_contra he1
  have heQne : (⟨e, heQ⟩ : Q) ≠ 1 := by
    intro h
    exact he1 (by simpa using congrArg (fun z : Q => (z : G)) h)
  have hcent : e * x0 = x0 * e := by
    have hle : Subgroup.zpowers x0 ≤ Subgroup.centralizer ({x0} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
    exact ((Subgroup.mem_centralizer_iff.mp (hle heE)) x0 (Set.mem_singleton x0)).symm
  have hcoe_comm : e * (a : G) = (a : G) * e := by
    have h := (Subgroup.mem_center_iff.mp hacen) (⟨e, heQ⟩ : Q)
    exact congrArg (fun z : Q => (z : G)) h
  have haea : (a : G) * e * (a : G) = e := by
    calc (a : G) * e * (a : G) = (a : G) * (e * (a : G)) := by group
      _ = (a : G) * ((a : G) * e) := by rw [hcoe_comm]
      _ = ((a : G) * (a : G)) * e := by group
      _ = e := by rw [haa, one_mul]
  have hμe : e * μ = μ * e := by
    have h1 : e * (μ * (a : G)) = (μ * (a : G)) * e := hcent
    calc e * μ = e * μ * ((a : G) * (a : G)) := by rw [haa, mul_one]
      _ = e * (μ * (a : G)) * (a : G) := by group
      _ = (μ * (a : G)) * e * (a : G) := by rw [h1]
      _ = μ * ((a : G) * e * (a : G)) := by group
      _ = μ * e := by rw [haea]
  have htet : t * e * t = hG C a * e * (hG C a)⁻¹ := by
    have h3 : e * (t * hG C a) = (t * hG C a) * e := hμe
    have h4 : t * (e * t * hG C a) = hG C a * e := by
      have h3' : t * (e * t) * hG C a = hG C a * e := by
        calc t * (e * t) * hG C a = t * (e * (t * hG C a)) := by group
          _ = t * ((t * hG C a) * e) := by rw [h3]
          _ = (t * t) * (hG C a * e) := by group
          _ = hG C a * e := by rw [ht2, one_mul]
      calc t * (e * t * hG C a) = t * (e * t) * hG C a := by group
        _ = hG C a * e := h3'
    calc t * e * t = t * (e * t * hG C a) * (hG C a)⁻¹ := by group
      _ = (hG C a * e) * (hG C a)⁻¹ := by rw [h4]
      _ = hG C a * e * (hG C a)⁻¹ := by group
  have hmemQ : hG C a * e * (hG C a)⁻¹ ∈ Q := canon_D_conj_Q_mem hsplit (C.h a) ⟨e, heQ⟩
  have hmemH : t * e * t ∈ H := by rw [htet]; exact hsplit.le hmemQ
  have heQne' : (((⟨e, heQ⟩ : Q)) : G) ≠ 1 :=
    fun h => heQne (Subtype.ext (by simpa using h))
  exact (Work.ZassenhausPSL2.t_conj_notMem hsplit (x := ⟨e, heQ⟩) heQne') hmemH


/-- **`C_Q(μ) = 1`** for `μ = t · h a`. -/
theorem centralizer_hG_mul_t_inf_Q_eq_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q} :
    Subgroup.centralizer ({(t * hG C a)} : Set G) ⊓ Q = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxc, hxQ⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hcomm : x * (t * hG C a) = (t * hG C a) * x :=
    ((Subgroup.mem_centralizer_iff.mp hxc) (t * hG C a) (Set.mem_singleton _)).symm
  have htet : t * x * t = hG C a * x * (hG C a)⁻¹ := by
    have h2' : t * (x * t * hG C a) = hG C a * x := by
      calc t * (x * t * hG C a) = (t * x * t) * hG C a := by group
        _ = t * (x * (t * hG C a)) := by group
        _ = t * ((t * hG C a) * x) := by rw [hcomm]
        _ = (t * t) * (hG C a * x) := by group
        _ = hG C a * x := by rw [canon_t_mul_t hsplit, one_mul]
    calc t * x * t = t * (x * t * hG C a) * (hG C a)⁻¹ := by group
      _ = (hG C a * x) * (hG C a)⁻¹ := by rw [h2']
      _ = hG C a * x * (hG C a)⁻¹ := by group
  have hmemQ : hG C a * x * (hG C a)⁻¹ ∈ Q := canon_D_conj_Q_mem hsplit (C.h a) ⟨x, hxQ⟩
  have hmemH : t * x * t ∈ H := by rw [htet]; exact hsplit.le hmemQ
  have hxQne : (((⟨x, hxQ⟩ : Q)) : G) ≠ 1 := by
    intro h
    exact hx1 (by simpa using h)
  exact (Work.ZassenhausPSL2.t_conj_notMem hsplit (x := ⟨x, hxQ⟩) hxQne) hmemH

/-- **`C_Q(μ a) = 1`** for `a ∈ Z(Q)` a non-trivial involution and `μ = t · h a`. -/
theorem centralizer_mu_mul_a_inf_Q_eq_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q}
    (ha2 : a * a = 1) (hacen : a ∈ Subgroup.center Q) :
    Subgroup.centralizer ({(t * hG C a * (a : G))} : Set G) ⊓ Q = ⊥ := by
  have haa : (a : G) * (a : G) = 1 := by simpa using congrArg (fun z : Q => (z : G)) ha2
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxc, hxQ⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have hxx0 : (t * hG C a * (a : G)) * x = x * (t * hG C a * (a : G)) :=
    (Subgroup.mem_centralizer_iff.mp hxc) (t * hG C a * (a : G)) (Set.mem_singleton _)
  have hcoe : x * (a : G) = (a : G) * x := by
    have h := (Subgroup.mem_center_iff.mp hacen) (⟨x, hxQ⟩ : Q)
    exact congrArg (fun z : Q => (z : G)) h
  have haea : (a : G) * x * (a : G) = x := by
    calc (a : G) * x * (a : G) = (a : G) * (x * (a : G)) := by group
      _ = (a : G) * ((a : G) * x) := by rw [hcoe]
      _ = ((a : G) * (a : G)) * x := by group
      _ = x := by rw [haa, one_mul]
  have hxμ : (t * hG C a) * x = x * (t * hG C a) := by
    have h1 : (t * hG C a) * (a : G) * x = x * ((t * hG C a) * (a : G)) := hxx0
    calc (t * hG C a) * x
        = (t * hG C a) * x * ((a : G) * (a : G)) := by rw [haa, mul_one]
      _ = (t * hG C a) * (x * (a : G)) * (a : G) := by group
      _ = (t * hG C a) * ((a : G) * x) * (a : G) := by rw [hcoe]
      _ = ((t * hG C a) * (a : G)) * x * (a : G) := by group
      _ = (x * ((t * hG C a) * (a : G))) * (a : G) := by rw [h1]
      _ = x * ((t * hG C a) * ((a : G) * (a : G))) := by group
      _ = x * (t * hG C a) := by rw [haa, mul_one]
  have hmem : x ∈ Subgroup.centralizer ({(t * hG C a)} : Set G) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxμ), hxQ⟩
  rw [centralizer_hG_mul_t_inf_Q_eq_bot hsplit hzass h2 C] at hmem
  exact Subgroup.mem_bot.mp hmem


/-- **The normaliser of `⟨μ a⟩` in `Q` has a unique non-trivial involution, namely `a`.**
(BG 5.13: the automorphism of the cyclic group `⟨μ a⟩` induced by such an involution either has
a non-trivial fixed point — which by `C_H(s) ⊆ Q` and `E ∩ Q = 1` is impossible — or is the
inversion, which by `C_Q(⟨μ a⟩) = 1` forces the involution to be `a`.) -/
theorem eq_a_of_mem_normalizer_of_sq_eq_one {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q}
    (ha1 : (a : G) ≠ 1) (ha2 : a * a = 1) (hacen : a ∈ Subgroup.center Q)
    {τ : G} (hτQ : τ ∈ Q)
    (hτx0 : τ * (t * hG C a * (a : G)) * τ⁻¹
      ∈ Subgroup.zpowers (t * hG C a * (a : G)))
    (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) :
    τ = (a : G) := by
  set x0 : G := t * hG C a * (a : G) with hx0
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  have haa : (a : G) * (a : G) = 1 := by simpa using congrArg (fun z : Q => (z : G)) ha2
  have hμ2 : (t * hG C a) * (t * hG C a) = 1 := t_mul_h_sq hsplit hzass h2 C a
  have hEab : ∀ u ∈ Subgroup.zpowers x0, ∀ v ∈ Subgroup.zpowers x0, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  have hτx0' : τ * x0 * τ⁻¹ ∈ Subgroup.zpowers x0 := by
    rw [hx0]; rw [hx0] at hτx0; exact hτx0
  have hnorm : ∀ h : G, h ∈ Subgroup.zpowers x0 → τ * h * τ⁻¹ ∈ Subgroup.zpowers x0 := by
    intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hk]
    have hmap : τ * x0 ^ k * τ⁻¹ = (τ * x0 * τ⁻¹) ^ k := by
      rw [show τ * x0 ^ k * τ⁻¹ = (MulAut.conj τ) (x0 ^ k) from rfl, map_zpow]
      rfl
    rw [hmap]
    exact (Subgroup.zpowers x0).zpow_mem hτx0' k
  by_cases hfix : ∃ h ∈ Subgroup.zpowers x0, h ≠ 1 ∧ τ * h * τ⁻¹ = h
  · obtain ⟨h, hhE, hh1, hhh⟩ := hfix
    have hcomm : τ * h = h * τ := by
      have := congrArg (fun z : G => z * τ) hhh
      simpa [mul_assoc] using this
    have hhH : h ∈ H := commute_mem_H_of_mem_Q hsplit (s := ⟨τ, hτQ⟩) hτ1 hcomm
    have hτ2Q : (⟨τ, hτQ⟩ : Q) * ⟨τ, hτQ⟩ = 1 := Subtype.ext (by simpa using hτ2)
    have hhQ : h ∈ Q :=
      mem_H_centralizer_involution_le_Q hsplit hzass h2 hθ1 hθodd htorus
        (s := ⟨τ, hτQ⟩) hτ1 hτ2Q hhH hcomm
    have hmem : h ∈ Subgroup.zpowers x0 ⊓ Q := ⟨hhE, hhQ⟩
    rw [hx0, zpowers_mu_mul_a_inf_Q_eq_bot hsplit hzass h2 C ha1 ha2 hacen] at hmem
    exact absurd (Subgroup.mem_bot.mp hmem) hh1
  · push_neg at hfix
    have hx0E : x0 ∈ Subgroup.zpowers x0 := Subgroup.mem_zpowers x0
    have hφE : τ * x0 * τ⁻¹ ∈ Subgroup.zpowers x0 := hnorm x0 hx0E
    have hprodE : x0 * (τ * x0 * τ⁻¹) ∈ Subgroup.zpowers x0 :=
      (Subgroup.zpowers x0).mul_mem hx0E hφE
    have hfixed : τ * (x0 * (τ * x0 * τ⁻¹)) * τ⁻¹ = x0 * (τ * x0 * τ⁻¹) := by
      have h1 : τ * (x0 * (τ * x0 * τ⁻¹)) * τ⁻¹
          = (τ * x0 * τ⁻¹) * (τ * (τ * x0 * τ⁻¹) * τ⁻¹) := by group
      have h2 : τ * (τ * x0 * τ⁻¹) * τ⁻¹ = x0 := by
        have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
        rw [show τ * (τ * x0 * τ⁻¹) * τ⁻¹ = (τ * τ) * x0 * (τ⁻¹ * τ⁻¹) from by group,
          hτ2, one_mul, hτi, hτ2, mul_one]
      rw [h1, h2]
      exact hEab (τ * x0 * τ⁻¹) hφE x0 hx0E
    have hx0φ : x0 * (τ * x0 * τ⁻¹) = 1 := by
      by_contra hne
      exact hfix _ hprodE hne hfixed
    have hτx0 : τ * x0 * τ⁻¹ = x0⁻¹ := by
      have h := congrArg (fun z : G => x0⁻¹ * z) hx0φ
      simpa [mul_assoc] using h
    have hax0 : (a : G) * x0 * (a : G)⁻¹ = x0⁻¹ := by
      have h1 : (a : G) * x0 * (a : G)⁻¹ = (a : G) * (t * hG C a) := by
        conv_lhs => rw [hx0]
        exact mul_mul_mul_inv_cancel (a : G) (t * hG C a)
      have h2 : x0⁻¹ = (a : G) * (t * hG C a) := by
        rw [hx0, mul_inv_rev, inv_eq_of_mul_eq_one_right haa,
          inv_eq_of_mul_eq_one_right hμ2]
      rw [h1, h2]
    have hax0' : (a : G) * x0 * (a : G) = x0⁻¹ := by
      calc (a : G) * x0 * (a : G) = (a : G) * x0 * (a : G)⁻¹ := by
            rw [inv_eq_of_mul_eq_one_right haa]
        _ = x0⁻¹ := hax0
    have hcentral : (τ * (a : G)⁻¹) * x0 * (τ * (a : G)⁻¹)⁻¹ = x0 := by
      have h3 : (τ * (a : G)⁻¹) * x0 * (τ * (a : G)⁻¹)⁻¹
          = τ * ((a : G)⁻¹ * x0 * (a : G)) * τ⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        simp only [mul_assoc]
      rw [h3]
      have h4 : (a : G)⁻¹ * x0 * (a : G) = x0⁻¹ := by
        rw [show (a : G)⁻¹ = (a : G) from inv_eq_of_mul_eq_one_right haa]
        exact hax0'
      rw [h4, inv_conj_eq', hτx0, inv_inv]
    have hgx : (τ * (a : G)⁻¹) * x0 = x0 * (τ * (a : G)⁻¹) := by
      have h := congrArg (fun z : G => z * (τ * (a : G)⁻¹)) hcentral
      simpa [mul_assoc] using h
    have hmem : τ * (a : G)⁻¹ ∈ Subgroup.centralizer ({x0} : Set G) ⊓ Q :=
      ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hgx.symm),
        Q.mul_mem hτQ (Q.inv_mem a.2)⟩
    rw [hx0, centralizer_mu_mul_a_inf_Q_eq_bot hsplit hzass h2 C ha2 hacen] at hmem
    have h1 : τ * (a : G)⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc τ = τ * ((a : G) * (a : G)⁻¹) := by group
      _ = (τ * (a : G)⁻¹) * (a : G) := by group
      _ = (a : G) := by rw [h1, one_mul]


/-- `∼ a ≠ 1` for `a ≠ 1` (otherwise `f a = 1`). -/
theorem tildeOf_ne_one (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (C : Work.ZassenhausPSL2.Canon H Q t) {a : Q}
    (ha1 : (a : G) ≠ 1) : (tildeOf C a : Q) ≠ 1 := by
  intro h
  have h' := tildeOf_eq hsplit hzass h2 C ha1
  rw [h] at h'
  have : fG C a = 1 := by
    have := congrArg (fun z : G => (hG C a) * z * (hG C a)⁻¹) h'
    simpa [mul_assoc] using this.symm
  exact canon_f_ne_one hsplit C ha1 (by simpa using this)

/-- Helper: if `y * y = x` and `y` has the same order as `x`, then `y ∈ ⟨x⟩`. -/
theorem mem_zpowers_of_sq_eq {x y : G} (h : y * y = x) (hord : orderOf y = orderOf x) :
    y ∈ Subgroup.zpowers x := by
  haveI : Finite ↥(Subgroup.zpowers y) := Subtype.finite
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := by
    rw [← h]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_zpowers_iff.mpr ⟨2, by rw [zpow_ofNat]; exact pow_two y⟩)
  have hcard : Nat.card (Subgroup.zpowers y) = Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
  have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  rw [heq]
  exact Subgroup.mem_zpowers y

end Work.ZassenhausSuzuki

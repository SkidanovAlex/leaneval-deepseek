import Mathlib
import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Higman.Class
import Submission.Work.Hering.Step5.mulAut_eight_order21
import Submission.Work.Hering.HardCore.gl32_mulAut_V_iso
import Submission.Work.Hering.HardCore.SixtyfourSetup
import Submission.Work.Hering.GL32.singer_of_exp_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- A subgroup of exponent two is abelian (elementwise form). -/
private lemma comm_of_exp_two_q3 {G : Type} [Group G] (V : Subgroup G)
    (hexp : ∀ x ∈ V, x * x = 1) {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  have hx1 : x * x = 1 := hexp x hx
  have hxy : (x * y) * (x * y) = 1 := hexp (x * y) (V.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hexp y hy)
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [mul_inv_rev, hxinv, hyinv] at h2
  exact h2

/-- A non-abelian subgroup `D` of order `64` with `V ≤ D ≤ C = C_G(V)`, normal in `G`, is a
Suzuki 2-group with `|Z(D)| = 8`.

Proof route: `D ∩ Ω₁(C) = V` (from `hinv` and `D ≤ C`) and `V ⊆ Ω₁(D)` (from `hexpV`), hence
`Ω₁(D) = V`; `hHig.1` (`z ∈ Z(D) ↔ z² = 1`) then gives `Z(D) = V`, of order 8. For the Suzuki
structure, use `hAut` to get `g ∈ G` (e.g. via `mulAut_eight_order21` / `gl32_mulAut_V_iso`
and the Singer cycle) whose conjugation acts on `V` transitively on `V#`; `D.Normal` makes
`MulAut.conjNormal g ∈ MulAut ↥D`, and since every involution of `D` lies in `V`, this is a
cyclic group transitive on `Inv(D)` — the same pattern as `HardCore/isSuzuki_of_config`. -/
theorem q3_suzuki_sixtyfour {G : Type} [Group G] [Finite G]
    (hHig : Work.Higman.HigmanClassProp)
    (V C D : Subgroup G) (hV : V.Normal) (hcardV : Nat.card V = 8)
    (hexpV : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : Work.Hering.ActsAsAut V hV)
    (hnotab : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hVD : V ≤ D) (hDC : D ≤ C) (hDn : D.Normal) (hcardD : Nat.card D = 64)
    (hnonab : ¬ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) :
    Work.Hering.IsSuzukiTwoGroup ↥D ∧ Nat.card ↥(Subgroup.center ↥D) = 8 := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  have hSuzD : Work.Hering.IsSuzukiTwoGroup ↥D := by
    haveI : D.Normal := hDn
    have hD2 : IsPGroup 2 ↥D := hC2.to_le hDC
    let incl : ↥V →* ↥D := Subgroup.inclusion hVD
    have hincl_coe : ∀ v : ↥V, ((incl v : ↥D) : G) = (v : G) :=
      fun v => Subgroup.coe_inclusion hVD v
    refine ⟨hD2, ?_, ?_, ?_⟩
    · -- `D` is non-abelian
      push_neg at hnonab
      obtain ⟨x, hx, y, hy, hxy⟩ := hnonab
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h =>
        hxy (by simpa [Subgroup.coe_mul] using congrArg Subtype.val h)⟩
    · -- `D` has two distinct involutions: distinct non-identity elements of `V`
      have hcardF : Fintype.card ↥V = 8 := by rw [← Nat.card_eq_fintype_card]; exact hcardV
      have hlt : 1 < Fintype.card ↥V := by omega
      obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : ↥V)
      have hlt2 : ({1, a} : Finset ↥V).card < (Finset.univ : Finset ↥V).card := by
        have h : ({1, a} : Finset ↥V).card ≤ 2 := by
          have h' := Finset.card_insert_le (1 : ↥V) ({a} : Finset ↥V)
          simp only [Finset.card_singleton] at h'
          omega
        rw [Finset.card_univ, hcardF]; omega
      obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      refine ⟨incl a, incl b, ?_, ?_, ?_⟩
      · rw [← Subgroup.orderOf_coe (incl a), hincl_coe a]
        exact orderOf_eq_prime (by rw [pow_two]; exact hexpV a a.2) (fun h => ha (Subtype.ext h))
      · rw [← Subgroup.orderOf_coe (incl b), hincl_coe b]
        exact orderOf_eq_prime (by rw [pow_two]; exact hexpV b b.2) (fun h => hb.1 (Subtype.ext h))
      · intro h
        exact hb.2 (Subgroup.inclusion_injective hVD h).symm
    · -- a cyclic group of automorphisms of `D` transitive on its involutions: conjugation by
      -- an element realising the Singer cycle of `Aut(V)` on `V`
      obtain ⟨ξ, _hξord, hξtrans⟩ :=
        Work.Hering.GL32.singer_of_exp_two
          (fun x y : ↥V => Subtype.ext (comm_of_exp_two_q3 V hexpV x.2 y.2))
          (fun x : ↥V => Subtype.ext (hexpV x x.2)) hcardV
      obtain ⟨g, hg⟩ := hAut ξ
      let φ : MulAut ↥D := MulAut.conjNormal (H := D) g
      have hkey : ∀ v : ↥V, φ (incl v) = incl (ξ v) := by
        intro v
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, hincl_coe v, hincl_coe (ξ v), hg v]
      have hpow : ∀ k : ℕ, ∀ v : ↥V, (φ ^ k) (incl v) = incl ((ξ ^ k) v) := by
        intro k
        induction k with
        | zero => intro v; simp
        | succ k ih => intro v; simp only [pow_succ, MulAut.mul_apply, hkey, ih]
      refine ⟨φ, ?_⟩
      intro x y hx hy
      have hxV : (x : G) ∈ V := hinv (x : G) (hDC x.2) (by rw [Subgroup.orderOf_coe]; exact hx)
      have hyV : (y : G) ∈ V := hinv (y : G) (hDC y.2) (by rw [Subgroup.orderOf_coe]; exact hy)
      have hxne : x ≠ 1 := by
        intro h; rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
      have hyne : y ≠ 1 := by
        intro h; rw [h, orderOf_one] at hy; exact absurd hy (by norm_num)
      have ha1 : (⟨(x : G), hxV⟩ : ↥V) ≠ 1 := by
        intro h
        exact hxne (Subtype.ext (by have := congrArg Subtype.val h; simpa using this))
      have hb1 : (⟨(y : G), hyV⟩ : ↥V) ≠ 1 := by
        intro h
        exact hyne (Subtype.ext (by have := congrArg Subtype.val h; simpa using this))
      obtain ⟨k, hk⟩ := hξtrans ⟨(x : G), hxV⟩ ⟨(y : G), hyV⟩ ha1 hb1
      refine ⟨k, ?_⟩
      have hxe : incl ⟨(x : G), hxV⟩ = x := Subtype.ext (by rw [hincl_coe])
      have hye : incl ⟨(y : G), hyV⟩ = y := Subtype.ext (by rw [hincl_coe])
      rw [← hxe, ← hye, hpow k ⟨(x : G), hxV⟩, hk]
  refine ⟨hSuzD, ?_⟩
  -- the centre of `D` is exactly `V`
  obtain ⟨hcenter, -, -, -, -⟩ := hHig.1 ↥D hSuzD
  have hiff : ∀ z : ↥D, z ∈ Subgroup.center ↥D ↔ ((z : G) ∈ V) := by
    intro z
    rw [hcenter]
    constructor
    · intro hz
      have hz2 : (z : G) ^ 2 = 1 := by
        have h := congrArg (fun t : ↥D => (t : G)) hz
        simpa using h
      rcases eq_or_ne (z : G) 1 with h1 | h1
      · rw [h1]; exact V.one_mem
      · exact hinv (z : G) (hDC z.2) (orderOf_eq_prime hz2 h1)
    · intro hz
      show z ^ 2 = 1
      have hz2 : (z : G) * (z : G) = 1 := hexpV (z : G) hz
      exact Subtype.ext (by simpa [pow_two] using hz2)
  have hbij : Nat.card ↥(Subgroup.center ↥D) = Nat.card ↥V :=
    Nat.card_congr
      { toFun := fun z => ⟨((z : ↥D) : G), (hiff (z : ↥D)).mp z.2⟩
        invFun := fun v => ⟨⟨(v : G), hVD v.2⟩,
          (hiff ⟨(v : G), hVD v.2⟩).mpr
            (show ((⟨(v : G), hVD v.2⟩ : ↥D) : G) ∈ V from v.2)⟩
        left_inv := by rintro ⟨z, hz⟩; rfl
        right_inv := by rintro ⟨v, hv⟩; rfl }
  rw [hbij, hcardV]

end Work.Hering.HardCore

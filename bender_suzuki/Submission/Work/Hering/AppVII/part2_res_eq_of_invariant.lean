import Mathlib
import Submission.Work.Clifford.All
import Submission.Work.CharCore.Main
import Submission.Work.CharPrelim.extend_char_of_cyclic_quotient
import Submission.Work.Hering.AppVII.part2_quotient_cyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

open Classical

set_option linter.style.haveILetI false

noncomputable section

/-- Restriction is multiplicative with respect to the pointwise product of functions. -/
private theorem resFun_mul {G : Type*} [Group G] (N : Subgroup G) (f g : G → ℂ) :
    Work.Clifford.resFun N (f * g) = Work.Clifford.resFun N f * Work.Clifford.resFun N g := by
  funext n
  rfl

theorem part2_res_eq_of_invariant {H : Type*} [Group H] [Fintype H] {p : ℕ} (Q P : Subgroup H)
    [Fintype ↥P] (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (hp : p.Prime)
    (hPcard : Nat.card ↥P = p) {χ : H → ℂ} (hχ : χ ∈ Work.CharCore.Irr H)
    {θ : ↥Q → ℂ} (hθ : θ ∈ Work.Clifford.Irr ↥Q) (hinv : Work.Clifford.inertia Q θ = ⊤)
    {e : ℕ} (hres : Work.Clifford.resFun Q χ = (e : ℂ) • Work.Clifford.orbitSum Q θ) :
    e = 1 ∧ Work.Clifford.resFun Q χ = θ := by
  classical
  haveI hQnorm : Q.Normal := hQn
  haveI hQfin : Fintype ↥Q := Fintype.ofFinite _
  haveI hQfin' : Fintype (H ⧸ Q) := QuotientGroup.fintype Q
  -- ### `θ` is `H`-invariant, so its orbit is a singleton and `orbitSum Q θ = θ`.
  have hsing : Work.Clifford.charOrbit Q θ = {θ} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Work.Clifford.theta_mem_charOrbit θ, ?_⟩
    intro φ hφ
    rw [Work.Clifford.mem_charOrbit] at hφ
    obtain ⟨g, hg⟩ := hφ
    rw [← hg]
    exact (Work.Clifford.mem_inertia Q θ g).mp (by rw [hinv]; exact Subgroup.mem_top g)
  have horbit : Work.Clifford.orbitSum Q θ = θ := by
    rw [Work.Clifford.orbitSum_eq_sum, hsing, Finset.sum_singleton]
  -- hence `χ|_Q = e • θ`.
  have hres' : Work.Clifford.resFun Q χ = (e : ℂ) • θ := by rw [hres, horbit]
  -- ### `e ≠ 0`: otherwise `χ|_Q = 0`, contradicting `χ 1 ≠ 0`.
  have hθC : θ ∈ Work.CharCore.Irr ↥Q := (Work.Clifford.mem_Irr_charCore_iff).mp hθ
  have hchi1 : χ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hχ]
    exact Nat.cast_ne_zero.mpr (Work.CharCore.irrDeg_pos hχ).ne'
  have he0 : e ≠ 0 := by
    intro he
    apply hchi1
    have h1 : Work.Clifford.resFun Q χ = 0 := by rw [hres', he]; simp
    have h2 := congrFun h1 (1 : ↥Q)
    simpa using h2
  -- ### `θ` is a constituent of `χ|_Q`.
  have hconst : Work.Clifford.IsConstituentOf θ (Work.Clifford.resFun Q χ) := by
    unfold Work.Clifford.IsConstituentOf
    rw [hres', Work.Clifford.cfInner_smul_left,
      Work.Clifford.cfInner_eq_ite_of_mem_Irr hθ hθ]
    simp only [ite_true, mul_one]
    exact Nat.cast_ne_zero.mpr he0
  -- ### `H ⧸ Q` is cyclic (of order `p`), so `θ` extends to `H` across the cyclic quotient.
  obtain ⟨hcyc, -⟩ := part2_quotient_cyclic Q P hQn hinf hsup hp hPcard
  obtain ⟨φ, hφC, hext⟩ :=
    Work.CharPrelim.extend_char_of_cyclic_quotient (K := Q) hθC hinv hcyc
  have hφ : φ ∈ Work.Clifford.Irr H := (Work.Clifford.mem_Irr_charCore_iff).mpr hφC
  have hχCl : χ ∈ Work.Clifford.Irr H := (Work.Clifford.mem_Irr_charCore_iff).mpr hχ
  -- ### Gallagher: `χ = φ · Inf β` for the extension `φ` and some `β ∈ Irr (H ⧸ Q)`.
  obtain ⟨β, hβ⟩ :=
    Work.Clifford.gallagher (N := Q) hθ hinv hφ hext χ hχCl hconst
  obtain ⟨hβmem, hβeq⟩ := hβ.1
  -- ### `β` is linear, as `H ⧸ Q` is abelian.
  haveI hcycI : IsCyclic (H ⧸ Q) := hcyc
  haveI hcommQ : IsMulCommutative (H ⧸ Q) := IsCyclic.isMulCommutative
  have hβC : β ∈ Work.CharCore.Irr (H ⧸ Q) := (Work.Clifford.mem_Irr_charCore_iff).mp hβmem
  have hβdeg : β (1 : H ⧸ Q) = 1 := by
    rw [Work.CharCore.irrDeg_spec hβC, Work.CharCore.irrDeg_eq_one_of_commutative hβC]
    norm_num
  -- ### `χ|_Q = β 1 • θ = θ`.
  have hres_infl : Work.Clifford.resFun Q (Work.Clifford.inflateFun Q β) = fun _ => β 1 := by
    funext q
    show β (QuotientGroup.mk (q : H)) = β 1
    rw [show QuotientGroup.mk (q : H) = (1 : H ⧸ Q) from
      (QuotientGroup.eq_one_iff (q : H)).mpr q.2]
  have hres_smul : Work.Clifford.resFun Q χ = β 1 • θ := by
    rw [hβeq, resFun_mul, hext, hres_infl]
    funext q
    simp [Pi.mul_apply, Pi.smul_apply, mul_comm]
  -- ### Comparing with `χ|_Q = e • θ` at the identity: `e = β 1 = 1`.
  have hθ1 : θ (1 : ↥Q) ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hθC]
    exact Nat.cast_ne_zero.mpr (Work.CharCore.irrDeg_pos hθC).ne'
  have heq : (e : ℂ) = β 1 := by
    have h1 : (e : ℂ) • θ = β 1 • θ := by rw [← hres', hres_smul]
    have h2 : (e : ℂ) * θ (1 : ↥Q) = β 1 * θ (1 : ↥Q) := by
      have := congrFun h1 (1 : ↥Q)
      simpa [Pi.smul_apply] using this
    exact (mul_left_inj' hθ1).mp h2
  have he1 : e = 1 := by
    have : (e : ℂ) = 1 := by rw [heq, hβdeg]
    exact_mod_cast this
  exact ⟨he1, by rw [hres', he1]; simp⟩

end

end Work.Hering.AppVII

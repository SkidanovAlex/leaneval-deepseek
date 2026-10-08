import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.Structure
import Submission.Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le
import Submission.Work.GlaubermanZJ.Thm41.lowerCentralSeries_le_iterComm_sup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman (4.5)–(4.8): the numerical reduction `n ≤ 2`

Glauberman's proof of Theorem 4.1 (p. 1112) shows that if `n ≥ 1` is the least integer with
`[B,A;n]` abelian and `[B,A;n+1] = 1`, then `n ≤ 2`.  The argument only uses the fact that the
lower central series of `S = A ⊔ B` agrees with the iterated commutators `[B,A;k]` modulo
`[B,B]` (Glauberman (4.5)) and the classical `[γ_i,γ_j] ≤ γ_{i+j}`.

* `centerIn_sup_of_centerIn`: centrality passes from `S` to the subgroup `A ⊔ B`;
* `iterComm_abelian_le_two`: the numerical bound.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- If `[B,B]` is central in `S` and `A, B ≤ S`, then `[B,B]` is central in `A ⊔ B`. -/
theorem centerIn_sup_of_centerIn {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hZ : ⁅B, B⁆ ≤ Work.PGroup.centerIn S) :
    ⁅B, B⁆ ≤ Work.PGroup.centerIn (A ⊔ B) := by
  have hcent : ⁅B, B⁆ ≤ Subgroup.centralizer (S : Set G) :=
    hZ.trans (centerIn_le_centralizer S)
  intro x hx
  have hS'S : A ⊔ B ≤ S := sup_le hAS hBS
  have hxB : x ∈ B := Subgroup.commutator_le_self B hx
  rw [Work.PGroup.centerIn, Subgroup.mem_map]
  refine ⟨⟨x, (le_sup_right : B ≤ A ⊔ B) hxB⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro z
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hx) (z : G) (hS'S z.2))

/-- **Glauberman (4.5)–(4.8).**  Let `A ≤ S` be abelian, `B ≤ S` with `[B,B]` central in `S`,
and let `n ≥ 1` be the least integer with `[B,A;n]` abelian.  If `[B,A;n+1] = 1`, then `n ≤ 2`. -/
theorem iterComm_abelian_le_two {S A B : Subgroup G} (n : ℕ)
    (hAS : A ≤ S) (hBS : B ≤ S) (hBn : S ≤ Subgroup.normalizer (B : Set G))
    (hAab : IsMulCommutative A) (hZ : ⁅B, B⁆ ≤ Work.PGroup.centerIn S)
    (hn1 : 1 ≤ n)
    (hnmin : ∀ k, 1 ≤ k → k < n → ¬ IsMulCommutative (iterComm B A k))
    (hbot : iterComm B A (n + 1) = ⊥) :
    n ≤ 2 := by
  set S' : Subgroup G := A ⊔ B with hS'def
  have hAS' : A ≤ S' := le_sup_left
  have hBS' : B ≤ S' := le_sup_right
  have hS'S : S' ≤ S := sup_le hAS hBS
  have hBn' : S' ≤ Subgroup.normalizer (B : Set G) := hS'S.trans hBn
  have hZ' : ⁅B, B⁆ ≤ Work.PGroup.centerIn S' := centerIn_sup_of_centerIn hAS hBS hZ
  -- (4.5) at `k = n+1`
  have h45 : S'.lowerCentralSeries (n + 1) ≤ iterComm B A (n + 1) ⊔ ⁅B, B⁆ :=
    Work.GlaubermanZJ.Thm41.lowerCentralSeries_le_iterComm_sup S' A B hAS' hBS'
      (le_of_eq hS'def.symm) hBn' hAab (n + 1) (by omega)
  -- hence `γ_{n+2}(S') = S'.lowerCentralSeries (n+1)` is contained in the centre ...
  have hgam : S'.lowerCentralSeries (n + 1) ≤ Work.PGroup.centerIn S' := by
    have h1 : S'.lowerCentralSeries (n + 1) ≤ ⁅B, B⁆ := by simpa [hbot] using h45
    exact h1.trans hZ'
  -- ... and therefore `γ_{n+3}(S') = S'.lowerCentralSeries (n+2) = 1`
  have hgam3 : S'.lowerCentralSeries (n + 2) = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hgam.trans (centerIn_le_centralizer S')
  -- `m = ⌊(n+4)/2⌋`
  set m : ℕ := (n + 4) / 2 with hmdef
  have hm2 : 2 ≤ m := by omega
  have hm2n : 2 * m ≤ n + 4 := by omega
  -- the `m`-th term `γ_m(S') = lowerCentralSeries (m-1)` is abelian
  have hgamm_ab : IsMulCommutative (S'.lowerCentralSeries (m - 1)) := by
    rw [← Subgroup.commutator_self_eq_bot_iff]
    refine le_bot_iff.mp ?_
    calc ⁅S'.lowerCentralSeries (m - 1), S'.lowerCentralSeries (m - 1)⁆
        ≤ S'.lowerCentralSeries ((m - 1) + (m - 1) + 1) :=
          Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le S' (m - 1) (m - 1)
      _ = S'.lowerCentralSeries (2 * m - 1) := by congr 1; omega
      _ ≤ S'.lowerCentralSeries (n + 2) :=
          Subgroup.lowerCentralSeries_antitone (S := S') (by omega)
      _ = ⊥ := hgam3
  -- `[B,A;m-1] ≤ γ_m(S')` is abelian, so `m - 1 ≥ n` by minimality of `n`
  have hmn : n ≤ m - 1 := by
    refine le_of_not_gt fun hlt => hnmin (m - 1) (by omega) hlt ?_
    refine Work.PGroup.isMulCommutative_of_le hgamm_ab ?_
    calc iterComm B A (m - 1)
        ≤ iterComm S' A (m - 1) :=
          iterComm_mono (le_sup_right : B ≤ S') le_rfl (m - 1)
      _ ≤ S'.lowerCentralSeries (m - 1) :=
          iterComm_le_lowerCentralSeries S' A (le_sup_left : A ≤ S') (m - 1)
  omega

end Work.GlaubermanZJ

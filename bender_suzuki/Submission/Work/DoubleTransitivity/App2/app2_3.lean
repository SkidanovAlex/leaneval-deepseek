import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix II (3): double transitivity from `p`-subgroups fixing pairs

This file proves `Work.DoubleTransitivity.App2.app2_3`, the formalisation of Peterfalvi,
*Le théorème de Bender–Suzuki I*, Appendix II (3):

> Suppose that for every `c ∈ E \ {a}`, `{a, c}` is the set of fixed points of a `p`-subgroup
> of `X`, and that `X` does not fix `a`.  Then `X` acts 2-transitively on `E`.

The proof follows the source: for each `c ≠ a` one produces a `p`-Sylow `Q_c` of the point
stabiliser `H = X_a` with fixed-point set exactly `{a, c}` (this is where the `p`-Sylow of the
two-point stabiliser `H ∩ X_c` enters, via the normalizer argument of App. II (1)); two such
Sylows are conjugate inside `H` (Sylow's theorem), and conjugating `Q_b` to `Q_c` by an element
`x ∈ H` carries the fixed set `{a, b}` to `{a, c}`, so `x • b = c`.  Hence `H` is transitive on
`E \ {a}`; since `X` does not fix `a`, this makes the action 2-transitive.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.DoubleTransitivity.App2

open Work.DoubleTransitivity

variable {X E : Type} [Group X] [MulAction X E]

/-! ## Auxiliary lemmas -/

/-- Conjugation carries the set of fixed points of a subgroup to the set of fixed points of the
conjugate subgroup: `E_{gPg⁻¹} = g · E_P`. -/
theorem app2_3_fixedBySub_map_conj (P : Subgroup X) (g : X) :
    fixedBySub (X := X) (E := E) (P.map (MulAut.conj g).toMonoidHom) =
      g • fixedBySub (X := X) (E := E) P := by
  ext y
  rw [mem_fixedBySub, Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBySub]
  constructor
  · intro hy m hm
    have h1 : MulAut.conj g m ∈ P.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hm
    have h2 : (MulAut.conj g m) • y = y := hy _ h1
    rw [MulAut.conj_apply, mul_smul, mul_smul] at h2
    exact (smul_eq_iff_eq_inv_smul g).mp h2
  · intro hy n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    change (MulAut.conj g m) • y = y
    rw [MulAut.conj_apply, mul_smul, mul_smul, hy m hm, smul_inv_smul]

/-- The natural action of `MulAut.conj x` on the subgroups of `↥H` is `Subgroup.map`. -/
theorem app2_3_mulAut_conj_smul_eq_map {H : Subgroup X} (x : ↥H) (K : Subgroup ↥H) :
    MulAut.conj x • K = K.map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- Conjugation inside a subgroup agrees with conjugation in the ambient group. -/
theorem app2_3_subtype_comp_conj (H : Subgroup X) (x : ↥H) :
    H.subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : X)).toMonoidHom.comp H.subtype := by
  ext y
  simp [MulAut.conj_apply]

/-- In a finite `p`-group, a subgroup which equals its own normalizer is the whole group. -/
theorem app2_3_eq_of_isPGroup_normalizer_inf_eq [Finite X] {p : ℕ} [Fact p.Prime]
    {Q R : Subgroup X} (hR : IsPGroup p R) (hQR : Q ≤ R)
    (hN : Subgroup.normalizer (Q : Set X) ⊓ R = Q) : R = Q := by
  haveI : Group.IsNilpotent ↥R := IsPGroup.isNilpotent hR
  have hnc : NormalizerCondition ↥R := Group.normalizerCondition_of_isNilpotent
  have hnorm : Subgroup.normalizer ((Q.subgroupOf R : Set ↥R)) = Q.subgroupOf R := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQR]
    show (Subgroup.normalizer (Q : Set X)).subgroupOf R = Q.subgroupOf R
    conv_rhs => rw [← hN]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2, and_true]
  have htop : Q.subgroupOf R = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) (Q.subgroupOf R) hnorm
  have hRQ : R ≤ Q := fun x hx => by
    have hx' : (⟨x, hx⟩ : ↥R) ∈ Q.subgroupOf R := by rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf).mp hx'
  exact le_antisymm hRQ hQR

/-- Peterfalvi, Appendix II (1), structural part: if `Q` is a `p`-Sylow of the subgroup `D ≤ H`
and its normalizer inside `H` already lies in `D`, then `Q` is (the image of) a `p`-Sylow of `H`
as well. -/
theorem app2_3_sylow_map_subtype_eq [Finite X] {p : ℕ} [Fact p.Prime]
    {D H : Subgroup X} (hDH : D ≤ H) (Qd : Sylow p ↥D)
    (hN : Subgroup.normalizer (((Qd : Subgroup ↥D).map D.subtype : Subgroup X) : Set X) ⊓ H ≤ D) :
    ∃ Qh : Sylow p ↥H, (Qh : Subgroup ↥H).map H.subtype = (Qd : Subgroup ↥D).map D.subtype := by
  set Qx : Subgroup X := (Qd : Subgroup ↥D).map D.subtype with hQx
  have hQxleD : Qx ≤ D := Subgroup.map_subtype_le _
  have hQxleH : Qx ≤ H := hQxleD.trans hDH
  have hQxpg : IsPGroup p Qx := Qd.isPGroup'.map D.subtype
  have hQxHpg : IsPGroup p (Qx.subgroupOf H) := hQxpg.comap_subtype
  have hsubD : Qx.subgroupOf D = (Qd : Subgroup ↥D) := by
    rw [hQx, ← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  refine ⟨⟨Qx.subgroupOf H, hQxHpg, ?_⟩, ?_⟩
  · intro R hR hle
    set Rx : Subgroup X := R.map H.subtype with hRx
    have hRxpg : IsPGroup p Rx := hR.map H.subtype
    have hRxH : Rx ≤ H := Subgroup.map_subtype_le R
    have hQxRx : Qx ≤ Rx := by
      have h1 : (Qx.subgroupOf H).map H.subtype ≤ Rx := Subgroup.map_mono hle
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQxleH] at h1
    set M : Subgroup X := Subgroup.normalizer (Qx : Set X) ⊓ Rx with hM
    have hMpg : IsPGroup p M := hRxpg.to_le inf_le_right
    have hMleD : M ≤ D :=
      fun x hx => hN (le_inf inf_le_left (le_trans inf_le_right hRxH) hx)
    have hQxM : Qx ≤ M := le_inf Subgroup.le_normalizer hQxRx
    have hMsubD : (Qd : Subgroup ↥D) ≤ M.subgroupOf D := by
      rw [← hsubD]
      exact fun x hx => hQxM hx
    have hMeq : M = Qx := by
      have hmax : M.subgroupOf D = (Qd : Subgroup ↥D) :=
        Qd.is_maximal' hMpg.comap_subtype hMsubD
      have h1 : M = (M.subgroupOf D).map D.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMleD]
      rw [h1, hmax, hQx]
    have hNQx : Subgroup.normalizer (Qx : Set X) ⊓ Rx = Qx := by rw [← hM, hMeq]
    have hRxQx : Rx = Qx := app2_3_eq_of_isPGroup_normalizer_inf_eq hRxpg hQxRx hNQx
    have h1 : R = (R.map H.subtype).subgroupOf H := by
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
    rw [h1, ← hRx, hRxQx]
  · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQxleH]

/-- Peterfalvi, Appendix II (1), normalizer part: if a subgroup `Q` (with `Q ≤ X_a`) has fixed
point set exactly `{a, c}`, then its normalizer inside `X_a` already lies in the two-point
stabiliser `X_a ∩ X_c`. -/
theorem app2_3_normalizer_inf_stabilizer_le (a c : E) (hac : c ≠ a) (Q : Subgroup X)
    (hQH : Q ≤ MulAction.stabilizer X a)
    (hfix : fixedBySub (X := X) (E := E) Q = {a, c}) :
    Subgroup.normalizer (Q : Set X) ⊓ MulAction.stabilizer X a ≤
      MulAction.stabilizer X a ⊓ MulAction.stabilizer X c := by
  intro x hx
  obtain ⟨hxN, hxH⟩ := hx
  have hax : x • a = a := MulAction.mem_stabilizer_iff.mp hxH
  have hconj : Q.map (MulAut.conj x).toMonoidHom = Q :=
    (conj_eq_self_iff_mem_normalizer x Q).mpr hxN
  have hset : x • (fixedBySub (X := X) (E := E) Q) = fixedBySub (X := X) (E := E) Q := by
    have h1 := app2_3_fixedBySub_map_conj (E := E) Q x
    rw [← h1, hconj]
  have hmem : x • c ∈ x • (fixedBySub (X := X) (E := E) Q) :=
    ⟨c, by rw [hfix]; simp, rfl⟩
  rw [hset, hfix] at hmem
  have hcu : x • c = c := by
    rcases hmem with h | h
    · exact absurd (smul_left_cancel x (h.trans hax.symm)) hac
    · exact h
  exact ⟨hxH, MulAction.mem_stabilizer_iff.mpr hcu⟩

/-- Peterfalvi, Appendix II (1) + (3), key step: for every `c ≠ a` there is a `p`-Sylow `Q` of
`H = X_a` whose fixed point set is exactly `{a, c}`. -/
theorem app2_3_exists_sylow [Finite X] {p : ℕ} [Fact p.Prime] {a c : E} (hac : c ≠ a)
    (h : ∃ P : Subgroup X, IsPGroup p P ∧ fixedBySub (X := X) (E := E) P = {a, c}) :
    ∃ Qh : Sylow p ↥(MulAction.stabilizer X a),
      fixedBySub (X := X) (E := E)
        ((Qh : Subgroup ↥(MulAction.stabilizer X a)).map
          (MulAction.stabilizer X a).subtype) = {a, c} := by
  obtain ⟨P, hPpg, hPfix⟩ := h
  have haP : a ∈ fixedBySub (X := X) (E := E) P := by rw [hPfix]; simp
  have hcP : c ∈ fixedBySub (X := X) (E := E) P := by rw [hPfix]; simp
  have hPleH : P ≤ MulAction.stabilizer X a := fun m hm =>
    MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp haP) m hm)
  have hPleXc : P ≤ MulAction.stabilizer X c := fun m hm =>
    MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hcP) m hm)
  set D : Subgroup X := MulAction.stabilizer X a ⊓ MulAction.stabilizer X c with hD
  have hPleD : P ≤ D := by rw [hD]; exact le_inf hPleH hPleXc
  have hDH : D ≤ MulAction.stabilizer X a := by rw [hD]; exact inf_le_left
  have hDc : D ≤ MulAction.stabilizer X c := by rw [hD]; exact inf_le_right
  obtain ⟨Qd, hQd⟩ := IsPGroup.exists_le_sylow (hPpg.comap_subtype (K := D))
  set Qx : Subgroup X := (Qd : Subgroup ↥D).map D.subtype with hQx
  have hPleQx : P ≤ Qx := by
    have h1 : (P.subgroupOf D).map D.subtype ≤ Qx := by
      rw [hQx]; exact Subgroup.map_mono hQd
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPleD] at h1
  have hQxleD : Qx ≤ D := by rw [hQx]; exact Subgroup.map_subtype_le _
  have hQxleH : Qx ≤ MulAction.stabilizer X a := hQxleD.trans hDH
  have hQxleXc : Qx ≤ MulAction.stabilizer X c := hQxleD.trans hDc
  have hQxfix : fixedBySub (X := X) (E := E) Qx = {a, c} := by
    apply Set.Subset.antisymm
    · have hsub := fixedBySub_antitone (X := X) (E := E) hPleQx
      rwa [hPfix] at hsub
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact mem_fixedBySub.mpr fun m hm => MulAction.mem_stabilizer_iff.mp (hQxleH hm)
      · exact mem_fixedBySub.mpr fun m hm => MulAction.mem_stabilizer_iff.mp (hQxleXc hm)
  have hN : Subgroup.normalizer (Qx : Set X) ⊓ MulAction.stabilizer X a ≤ D := by
    rw [hD]
    exact app2_3_normalizer_inf_stabilizer_le a c hac Qx hQxleH hQxfix
  obtain ⟨Qh, hQh⟩ := app2_3_sylow_map_subtype_eq hDH Qd hN
  exact ⟨Qh, by rw [hQh, hQxfix]⟩

/-! ## The main statement -/

theorem app2_3 {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {a : E}
    (h : ∀ c ∈ ({a}ᶜ : Set E), ∃ P : Subgroup X, IsPGroup p P ∧ fixedBySub P = {a, c})
    (hfix : ¬ ∀ x : X, x • a = a) :
    MulAction.IsMultiplyPretransitive X E 2 := by
  have hg0 : ∃ g : X, g • a ≠ a := not_forall.mp hfix
  -- `X_a` is transitive on `E \ {a}`.
  have htransH : ∀ u v : E, u ≠ a → v ≠ a →
      ∃ x : X, x ∈ MulAction.stabilizer X a ∧ x • u = v := by
    intro u v hu hv
    obtain ⟨Qu, hQu⟩ := app2_3_exists_sylow (p := p) (a := a) (c := u) hu
      (h u (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu))
    obtain ⟨Qv, hQv⟩ := app2_3_exists_sylow (p := p) (a := a) (c := v) hv
      (h v (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hv))
    haveI : MulAction.IsPretransitive ↥(MulAction.stabilizer X a)
        (Sylow p ↥(MulAction.stabilizer X a)) :=
      Sylow.isPretransitive_of_finite
    obtain ⟨x, hx⟩ :=
      MulAction.IsPretransitive.exists_smul_eq (M := ↥(MulAction.stabilizer X a)) Qu Qv
    have hcoe : (Qu : Subgroup ↥(MulAction.stabilizer X a)).map (MulAut.conj x).toMonoidHom =
        (Qv : Subgroup ↥(MulAction.stabilizer X a)) := by
      have h1 := congrArg (fun S : Sylow p ↥(MulAction.stabilizer X a) =>
        (S : Subgroup ↥(MulAction.stabilizer X a))) hx
      rw [Sylow.coe_subgroup_smul] at h1
      rwa [app2_3_mulAut_conj_smul_eq_map] at h1
    have hconj : ((Qu : Subgroup ↥(MulAction.stabilizer X a)).map
            (MulAction.stabilizer X a).subtype).map
          (MulAut.conj (x : X)).toMonoidHom =
        (Qv : Subgroup ↥(MulAction.stabilizer X a)).map
          (MulAction.stabilizer X a).subtype := by
      have h2 := congrArg (Subgroup.map (MulAction.stabilizer X a).subtype) hcoe
      rw [Subgroup.map_map] at h2
      rw [app2_3_subtype_comp_conj] at h2
      rw [← Subgroup.map_map] at h2
      exact h2
    have hset : (x : X) • ({a, u} : Set E) = ({a, v} : Set E) := by
      rw [← hQu, ← app2_3_fixedBySub_map_conj, hconj, hQv]
    refine ⟨x, x.2, ?_⟩
    have hax : (x : X) • a = a := MulAction.mem_stabilizer_iff.mp x.2
    have hmem : (x : X) • u ∈ ({a, v} : Set E) := by
      rw [← hset]
      exact ⟨u, by simp, rfl⟩
    rw [Set.mem_insert_iff] at hmem
    rcases hmem with hh | hh
    · exact absurd (smul_left_cancel (x : X) (hh.trans hax.symm)) hu
    · rwa [Set.mem_singleton_iff] at hh
  -- the orbit of `a` is all of `E`.
  have h_orbit : ∀ u : E, ∃ x : X, x • a = u := by
    intro u
    by_cases hu : u = a
    · exact ⟨1, by rw [one_smul, hu]⟩
    · obtain ⟨g0, hg0⟩ := hg0
      obtain ⟨x, _, hx⟩ := htransH (g0 • a) u hg0 hu
      exact ⟨x * g0, by rw [mul_smul, hx]⟩
  have htransX : ∀ u v : E, ∃ x : X, x • u = v := by
    intro u v
    obtain ⟨y, hy⟩ := h_orbit u
    obtain ⟨z, hz⟩ := h_orbit v
    refine ⟨z * y⁻¹, ?_⟩
    have hyu : y⁻¹ • u = a := by rw [← hy, inv_smul_smul]
    rw [mul_smul, hyu, hz]
  -- therefore the stabiliser of every point is transitive on the complement.
  have htrans_stab : ∀ c u v : E, u ≠ c → v ≠ c →
      ∃ x : X, x • c = c ∧ x • u = v := by
    intro c u v hu hv
    obtain ⟨y0, hy0⟩ := h_orbit c
    have hu' : y0⁻¹ • u ≠ a := by
      intro hh
      exact hu (by rw [← hy0, ← hh, smul_inv_smul])
    have hv' : y0⁻¹ • v ≠ a := by
      intro hh
      exact hv (by rw [← hy0, ← hh, smul_inv_smul])
    obtain ⟨x, hxH, hx⟩ := htransH (y0⁻¹ • u) (y0⁻¹ • v) hu' hv'
    refine ⟨y0 * x * y0⁻¹, ?_, ?_⟩
    · have hy0a : y0⁻¹ • c = a := by rw [← hy0, inv_smul_smul]
      have hxa : x • a = a := MulAction.mem_stabilizer_iff.mp hxH
      show (y0 * x * y0⁻¹) • c = c
      rw [mul_smul, mul_smul, hy0a, hxa, hy0]
    · show (y0 * x * y0⁻¹) • u = v
      rw [mul_smul, mul_smul, hx, smul_inv_smul]
  refine ⟨fun f g => ?_⟩
  obtain ⟨y, hy⟩ := htransX (f 0) (g 0)
  have hne : y • f 1 ≠ g 0 := by
    intro hcontra
    rw [← hy] at hcontra
    exact Fin.zero_ne_one (f.injective (smul_left_cancel y hcontra).symm)
  have hne2 : g 1 ≠ g 0 := fun hc => Fin.zero_ne_one (g.injective hc).symm
  obtain ⟨h', hh'c, hh'⟩ := htrans_stab (g 0) (y • f 1) (g 1) hne hne2
  refine ⟨h' * y, ?_⟩
  ext i
  fin_cases i
  · show (h' * y) • f 0 = g 0
    rw [mul_smul, hy, hh'c]
  · show (h' * y) • f 1 = g 1
    rw [mul_smul, hh']

end Work.DoubleTransitivity.App2

import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.A7Fusion
import Submission.Work.CORE4.InvolutiveAutFixedInvolution

namespace Work.CORE4

open Work.GW2 Subgroup

section Helpers

/-- Membership in `conjSub z K`: being `z * a * z⁻¹` with `a ∈ K`. -/
theorem mem_conjSub_iff' {G : Type} [Group G] (K : Subgroup G) (z x : G) :
    x ∈ Work.GW2.conjSub z K ↔ ∃ a ∈ K, z * a * z⁻¹ = x := by
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, by rw [← hax]; rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- If `y` is an involution and `N` is a subgroup with `y N y⁻¹ ⊆ N`, then conjugation by `y`
induces an involutive automorphism of `N`.  When `|N|` is even, that automorphism fixes a
non-trivial involution of `N` (a parity argument: the complement of the fixed-point subgroup is
partitioned into 2-element orbits, so the fixed-point subgroup has even order and hence contains
an element of order `2`). -/
theorem involution_fixed_of_invariant {G : Type} [Group G] [Finite G]
    (N : Subgroup G) (y : G) (hy2 : y * y = 1)
    (hN : ∀ n : G, n ∈ N → y * n * y⁻¹ ∈ N) (heven : Even (Nat.card ↥N)) :
    ∃ c : G, c ∈ N ∧ c ≠ 1 ∧ c * c = 1 ∧ y * c * y⁻¹ = c := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hfix : ∀ n : ↥N, y * (y * (n : G) * y⁻¹) * y⁻¹ = (n : G) := by
    intro n
    rw [hyinv]
    calc y * (y * ↑n * y) * y = (y * y) * ↑n * (y * y) := by group
      _ = ↑n := by rw [hy2]; simp
  let σ : ↥N ≃* ↥N :=
    { toFun := fun n => ⟨y * (n : G) * y⁻¹, hN _ n.2⟩
      invFun := fun n => ⟨y * (n : G) * y⁻¹, hN _ n.2⟩
      left_inv := fun n => Subtype.ext (hfix n)
      right_inv := fun n => Subtype.ext (hfix n)
      map_mul' := by
        intro a b
        apply Subtype.ext
        show y * ((a : G) * (b : G)) * y⁻¹ =
          (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹)
        group }
  have hσ : σ * σ = 1 := by
    ext n
    show y * (y * (n : G) * y⁻¹) * y⁻¹ = (n : G)
    exact hfix n
  obtain ⟨c, hc1, hc2, hcfix⟩ :=
    Work.CORE4.InvolutiveAutFixedInvolution σ hσ heven
  refine ⟨(c : G), c.2, ?_, ?_, ?_⟩
  · intro h; exact hc1 (Subtype.ext h)
  · have := congr_arg Subtype.val hc2; simpa [pow_two] using this
  · have := congr_arg Subtype.val hcfix; simpa [σ] using this

end Helpers

/-- **`A7Normalize`** (Bender p. 226, the even case of `A6`): every involution `y ∉ M` with
`|M ∩ M^y|` even can be replaced, without changing the number `|I_{M∩M^y}(y)|` of elements of
`M ∩ M^y` inverted by `y`, by an involution `y' ∈ C_G(t)`.

Route.  `N := M ∩ M^y` is `y`-invariant, so `y` induces an involutive automorphism of `N`; since
`|N|` is even, `N` contains a non-trivial involution `c` fixed by `y` (`involution_fixed_of_invariant`,
which is `InvolutiveAutFixedInvolution` in disguise).  As `c ∈ M` is an involution, `A7Fusion`
gives `m ∈ M` with `m c m⁻¹ = t`.  Then `y' := m y m⁻¹` is an involution outside `M` centralizing
`t`, and conjugation by `m` identifies `I_N(y)` with `I_{M ∩ M^{y'}}(y')`, so the counts agree. -/
theorem A7Normalize (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D →
          ∀ y : G, orderOf y = 2 → y ∉ C.D.M →
            (¬ Odd (Nat.card ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M))) →
              ∃ y' : G, orderOf y' = 2 ∧ y' ∉ C.D.M ∧
                y' ∈ Subgroup.centralizer ({B.t} : Set G) ∧
                (Work.GW2.invSet (C.D.M ⊓ Work.GW2.conjSub y' C.D.M) y').ncard =
                  (Work.GW2.invSet (C.D.M ⊓ Work.GW2.conjSub y C.D.M) y).ncard := by
  intro G _inst _fin B C hHyp hA7 h1 h2 y hy2 hyM hnotodd
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  set N : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y C.D.M with hNdef
  have heven : Even (Nat.card ↥N) := Nat.not_odd_iff_even.mp hnotodd
  -- `N` is invariant under conjugation by `y`
  have hNinv : ∀ n : G, n ∈ N → y * n * y⁻¹ ∈ N := by
    intro n hn
    rw [hNdef] at hn ⊢
    obtain ⟨hnM, hnC⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨a, haM, ha⟩ := (mem_conjSub_iff' C.D.M y n).mp hnC
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : y * n * y⁻¹ = a := by
        rw [← ha, hyinv]
        calc y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = a := by rw [hyy]; simp
      rw [heq]; exact haM
    · exact (mem_conjSub_iff' C.D.M y (y * n * y⁻¹)).mpr ⟨n, hnM, rfl⟩
  -- a non-trivial involution `c ∈ N` fixed by `y`
  obtain ⟨c, hcN, hc1, hc2, hcfix⟩ := involution_fixed_of_invariant N y hyy hNinv heven
  have hcM : c ∈ C.D.M := by
    have h := hcN; rw [hNdef] at h; exact (Subgroup.mem_inf.mp h).1
  have hc2' : c ^ 2 = 1 := by rw [pow_two]; exact hc2
  have hcorder : orderOf c = 2 := orderOf_eq_prime hc2' hc1
  -- fusion: `c` is `M`-conjugate to `t`
  obtain ⟨m, hmM, hmc⟩ := A7Fusion I G B C hHyp hA7 h1 h2 c hcorder hcM
  set y' : G := m * y * m⁻¹ with hy'def
  set N' : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y' C.D.M with hN'def
  have hy'2 : orderOf y' = 2 := by
    rw [hy'def]
    have heq : m * y * m⁻¹ = (MulAut.conj m) y := by rw [MulAut.conj_apply]
    rw [heq, ← hy2, orderOf_eq_orderOf_iff]
    intro k
    rw [← map_pow]
    exact (MulAut.conj m).map_eq_one_iff
  have hy'M : y' ∉ C.D.M := by
    intro hy'M
    apply hyM
    have heq : y = m⁻¹ * y' * m := by rw [hy'def]; group
    rw [heq]
    exact C.D.M.mul_mem (C.D.M.mul_mem (C.D.M.inv_mem hmM) hy'M) hmM
  have hy'cen : y' ∈ Subgroup.centralizer ({B.t} : Set G) := by
    have hyt : y' * B.t * y'⁻¹ = B.t := by
      rw [hy'def, ← hmc]
      have hcomp : (m * y * m⁻¹) * (m * c * m⁻¹) * (m * y * m⁻¹)⁻¹
          = m * (y * c * y⁻¹) * m⁻¹ := by group
      rw [hcomp, hcfix]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y' * B.t = (y' * B.t * y'⁻¹) * y' := by group
      _ = B.t * y' := by rw [hyt]
  -- conjugation by `m` identifies the two inverted-element sets
  have hpres : (Work.GW2.invSet N' y').ncard = (Work.GW2.invSet N y).ncard := by
    refine (Set.ncard_congr (s := Work.GW2.invSet N y) (t := Work.GW2.invSet N' y')
      (fun x _ => m * x * m⁻¹) ?_ ?_ ?_).symm
    · intro x hx
      rw [Work.GW2.invSet] at hx ⊢
      obtain ⟨hxN, hxstep⟩ := hx
      have hxM : x ∈ C.D.M := by
        have h := hxN; rw [hNdef] at h; exact (Subgroup.mem_inf.mp h).1
      have hz : m * x * m⁻¹ ∈ C.D.M :=
        C.D.M.mul_mem (C.D.M.mul_mem hmM hxM) (C.D.M.inv_mem hmM)
      have hkey : y' * (m * x * m⁻¹) * y'⁻¹ = (m * x * m⁻¹)⁻¹ := by
        rw [hy'def]
        have hc : (m * y * m⁻¹) * (m * x * m⁻¹) * (m * y * m⁻¹)⁻¹
            = m * (y * x * y⁻¹) * m⁻¹ := by group
        rw [hc, hxstep]
        group
      have hz' : y' * (m * x * m⁻¹)⁻¹ * y'⁻¹ = m * x * m⁻¹ := by
        have h : y' * (m * x * m⁻¹)⁻¹ * y'⁻¹
            = (y' * (m * x * m⁻¹) * y'⁻¹)⁻¹ := by group
        rw [h, hkey]
        group
      refine ⟨?_, hkey⟩
      rw [hN'def]
      exact Subgroup.mem_inf.mpr ⟨hz,
        (mem_conjSub_iff' C.D.M y' (m * x * m⁻¹)).mpr ⟨(m * x * m⁻¹)⁻¹,
          C.D.M.inv_mem hz, hz'⟩⟩
    · intro a b _ _ hab
      rw [← MulAut.conj_apply m a, ← MulAut.conj_apply m b] at hab
      exact (MulAut.conj m).injective hab
    · intro b hb
      rw [Work.GW2.invSet] at hb
      obtain ⟨hbN', hbstep⟩ := hb
      have hbM : b ∈ C.D.M := by
        have h := hbN'; rw [hN'def] at h; exact (Subgroup.mem_inf.mp h).1
      set a : G := m⁻¹ * b * m with hadef
      have haM : a ∈ C.D.M := by
        rw [hadef]
        exact C.D.M.mul_mem (C.D.M.mul_mem (C.D.M.inv_mem hmM) hbM) hmM
      have ham : m * a * m⁻¹ = b := by rw [hadef]; group
      have hastepf : y * a * y⁻¹ = a⁻¹ := by
        have h : y * a * y⁻¹ = m⁻¹ * (y' * b * y'⁻¹) * m := by
          rw [hadef, hy'def]
          group
        rw [h, hbstep, hadef]
        group
      have hyainv : y * a⁻¹ * y⁻¹ = a := by
        have h : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
        rw [h, hastepf]
        group
      refine ⟨a, ?_, ham⟩
      rw [Work.GW2.invSet]
      refine ⟨?_, hastepf⟩
      rw [hNdef]
      exact Subgroup.mem_inf.mpr ⟨haM,
        (mem_conjSub_iff' C.D.M y a).mpr ⟨a⁻¹, C.D.M.inv_mem haM, hyainv⟩⟩
  exact ⟨y', hy'2, hy'M, hy'cen, hpres⟩

end Work.CORE4

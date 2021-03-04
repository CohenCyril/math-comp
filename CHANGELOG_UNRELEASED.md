# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `bigop.v`, added lemmas `sumnB`, `big_rcons`, `big_rcons_idx`,
  and `big_change_idx`.

- in `seq.v`,
  + new higher-order predicate `pairwise r xs` which asserts that the relation
    `r` holds for any i-th and j-th element of `xs` such that i < j.
  + new lemmas `allrel_mask(l|r)`, `allrel_filter(l|r)`, `sub(_in)_allrel`,
    `pairwise_cons`, `pairwise_cat`, `pairwise_rcons`, `pairwise2`,
    `pairwise_mask`, `pairwise_filter`, `pairwiseP`, `pairwise_all2rel`,
    `sub(_in)_pairwise`, `eq(_in)_pairwise`, `pairwise_map`, `subseq_pairwise`,
    `uniq_pairwise`, `pairwise_uniq`, and `pairwise_eq`.

- in `path.v`, new lemmas: `sorted_pairwise(_in)`, `path_pairwise(_in)`,
  `cycle_all2rel(_in)`, `pairwise_sort`, and `sort_pairwise_stable`.

- in `interval.v`, new lemmas: `ge_pinfty`, `le_ninfty`, `gt_pinfty`, `lt_ninfty`.

### Changed

- In `ssralg.v` and `ssrint.v`, the nullary ring notations `-%R`, `+%R`, `*%R`,
  `*:%R`, and `*~%R` are now declared in `fun_scope`.

- across the library, the deprecation mechanism to use has been changed from the
  `deprecate` notation to the `deprecated` attribute (cf. Removed section).

### Renamed

- in `path.v`,
  + `sub_(path|cycle|sorted)_in` -> `sub_in_(path|cycle|sorted)`
  + `eq_(path|cycle)_in` -> `eq_in_(path|cycle)`

### Removed

- in `ssreflect.v`, the `deprecate` notation has been deprecated. Use the
  `deprecated` attribute instead (cf. Changed section).

- in `seq.v`, `iota_add` has been deprecated. Use `iotaD` instead.

- in `ssrnat.v` and `ssrnum.v`, deprecation aliases and the `mc_1_10`
  compatibility modules introduced in MathComp 1.11+beta1 have been removed.

- in `seq.v`, remove the following deprecation aliases introduced in MathComp
  1.9.0: `perm_eq_rev`, `perm_eq_flatten`, `perm_eq_all`, `perm_eq_small`,
  `perm_eq_nilP`, `perm_eq_consP`, `leq_size_perm`, `uniq_perm_eq`,
  `perm_eq_iotaP`, and `perm_undup_count`.

### Infrastructure

### Misc
